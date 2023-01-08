(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the interface for the memory model that
  is used in the dynamic semantics of all the languages used in the compiler.
  It defines a type [mem] of memory states, the following 4 basic
  operations over memory states, and their properties:
- [load]: read a memory chunk at a given address;
- [store]: store a memory chunk at a given address;
- [alloc]: allocate a fresh memory block;
- [free]: invalidate a memory block.
*)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memdata.
Require Import Tags.

(** Memory states are accessed by addresses [b, ofs]: pairs of a block
  identifier [b] and a byte offset [ofs] within that block.
  Each address is associated to permissions, also known as access rights.
  The following permissions are expressible:
- Freeable (exclusive access): all operations permitted
- Writable: load, store and pointer comparison operations are permitted,
  but freeing is not.
- Readable: only load and pointer comparison operations are permitted.
- Nonempty: valid, but only pointer comparisons are permitted.
- Empty: not yet allocated or previously freed; no operation permitted.

The first four cases are represented by the following type of permissions.
Being empty is represented by the absence of any permission.
*)

Inductive permission: Type :=
| Live: permission          (* Allocated: reads and writes always succeed *)
| MostlyDead: permission    (* Not allocated, but not shadowed by compiler data *) 
| Dead: permission          (* Shadowed by compiler data *)
.

Module Type MEM (P:Policy).
  Module TLib := TagLib P.
  Import TLib.
  Module MD := Memdata P.
  Import MD.

(** The abstract type of memory states. *)
Parameter mem: Type.

(** * Operations on memory states *)

(** [empty] is the initial memory state. *)
Parameter empty: mem.

(** [alloc m lo hi] allocates a fresh block of size [hi - lo] bytes.
  Valid offsets in this block are between [lo] included and [hi] excluded.
  These offsets are writable in the returned memory state.
  This block is not initialized: its contents are initially undefined.
  Returns a pair [(m', b)] of the updated memory state [m'] and
  the identifier [b] of the newly-allocated block.
  Note that [alloc] never fails: we are modeling an infinite memory. *)
Parameter alloc: forall (m: mem) (lo hi: Z), option (mem * Z * Z).

(** [free m b lo hi] frees (deallocates) the range of offsets from [lo]
  included to [hi] excluded in block [b].  Returns the updated memory
  state, or [None] if the freed addresses are not freeable. *)
Parameter free: forall (m: mem) (lo hi: Z), option mem.

(** [load chunk m b ofs] reads a memory quantity [chunk] from
  addresses [b, ofs] to [b, ofs + size_chunk chunk - 1] in memory state
  [m].  Returns the value read, or [None] if the accessed addresses
  are not readable. *)
Parameter load: forall (chunk: memory_chunk) (m: mem) (ofs: Z), option atom.
Parameter load_ltags: forall (chunk: memory_chunk) (m: mem) (ofs: Z), list tag.

Axiom load_val_has_ltags :
  forall chunk m ofs,
    (exists v, load chunk m ofs = Some v /\ v <> (Vundef,def_tag)) <->
      (exists lts, load_ltags chunk m ofs = lts /\ length lts = size_chunk_nat chunk).

(** [store chunk m b ofs v] writes value [v] as memory quantity [chunk]
  from addresses [b, ofs] to [b, ofs + size_chunk chunk - 1] in memory state
  [m].  Returns the updated memory state, or [None] if the accessed addresses
  are not writable. *)
Parameter store:
  forall (chunk: memory_chunk)
         (m: mem)
         (ofs: Z)
         (a: atom)
         (lts: list tag), option mem.

(** [loadv] and [storev] are variants of [load] and [store] where
  the address being accessed is passed as a value (of the [Vptr] kind). *)

Definition loadv (chunk: memory_chunk) (m: mem) (addr: val) : option atom :=
  match addr with
  | Vint ofs => load chunk m (Int.unsigned ofs)
  | _ => None
  end.

Definition loadv_ltags (chunk: memory_chunk) (m: mem) (addr: val) : list tag :=
  match addr with
  | Vint ofs => load_ltags chunk m (Int.unsigned ofs)
  | _ => nil
  end.

Definition storev (chunk: memory_chunk) (m: mem) (addr: val) (a: atom) (lts: list tag) : option mem :=
  match addr with
  | Vint ofs => store chunk m (Int.unsigned ofs) a lts
  | _ => None
  end.

(** [loadbytes m b ofs n] reads and returns the byte-level representation of
  the values contained at offsets [ofs] to [ofs + n - 1] within block [b]
  in memory state [m].
  [None] is returned if the accessed addresses are not readable. *)
Parameter loadbytes: forall (m: mem) (ofs n: Z), option (list memval).
Parameter loadtags: forall (m: mem) (ofs n: Z), option (list tag).

(** [storebytes m b ofs bytes] stores the given list of bytes [bytes]
  starting at location [(b, ofs)].  Returns updated memory state
  or [None] if the accessed locations are not writable. *)
Parameter storebytes:
  forall (m: mem)
         (ofs: Z)
         (bytes: list memval)
         (ltag: list tag), option mem.

(** [free_list] frees all the given (block, lo, hi) triples. *)
Fixpoint free_list (m: mem) (l: list (Z * Z)) {struct l}: option mem :=
  match l with
  | nil => Some m
  | (lo, hi) :: l' =>
      match free m lo hi with
      | None => None
      | Some m' => free_list m' l'
      end
  end.

(** * Permissions, block validity, access validity, and bounds *)

(** The next block of a memory state is the block identifier for the
  next allocation.  It increases by one at each allocation.
  Block identifiers below [nextblock] are said to be valid if they are
  not freed. Block identifiers above [nextblock] are fresh or invalid,
  i.e. not yet allocated.  Note that
  a block identifier remains valid after a [free] operation over this
  block. *)

Parameter valid_addr : mem -> Z -> Prop.

Axiom valid_not_valid_diff:
  forall m a a', valid_addr m a -> ~(valid_addr m a') -> a <> a'.

(** [perm m b ofs k p] holds if the address [b, ofs] in memory state [m]
  has permission [p]. *)
Parameter perm: forall (m: mem) (ofs: Z) (p: permission), Prop.

(** [range_perm m b lo hi p] holds iff the addresses [b, lo] to [b, hi-1]
  all have permission [p]. *)
Definition range_perm (m: mem) (lo hi: Z) (p: permission) : Prop :=
  forall ofs, lo <= ofs < hi -> perm m ofs p.

Definition range_perm_neg (m: mem) (lo hi: Z) (p: permission) : Prop :=
  forall ofs, lo <= ofs < hi -> ~ perm m ofs p.

(** An access to a memory quantity [chunk] at address [b, ofs]
  is valid in [m] if the accessed addresses all have
  permission [Live] and moreover the offset is properly aligned. *)
Definition valid_access (m: mem) (chunk: memory_chunk) (ofs: Z) : Prop :=
  range_perm m ofs (ofs + size_chunk chunk) Live
  /\ (align_chunk chunk | ofs).

Axiom valid_access_valid_block:
  forall m chunk ofs,
    valid_access m chunk ofs ->
    valid_addr m ofs.

Axiom valid_block_valid_access:
  forall m chunk ofs,
    valid_addr m ofs ->
    valid_access m chunk ofs.

Axiom valid_access_perm:
  forall m chunk ofs,
    valid_access m chunk ofs ->
    perm m ofs Live.

(** An access to a memory quantity [chunk] at address [b, ofs] with
  permission [p] is allowed in [m] if none of the accessed addresses have
  permission [Dead] and the offset is properly aligned. *)

Definition allowed_access (m: mem) (chunk: memory_chunk) (ofs: Z) : Prop :=
  range_perm_neg m ofs (ofs + size_chunk chunk) Dead
  /\ (align_chunk chunk | ofs).

Axiom allowed_access_perm:
  forall m chunk ofs,
  allowed_access m chunk ofs ->
  ~ perm m ofs Dead.

Axiom valid_access_allowed:
  forall m chunk ofs,
    valid_access m chunk ofs ->
    allowed_access m chunk ofs.

(** [valid_pointer m b ofs] returns [true] if the address [b, ofs]
  is nonempty in [m] and [false] if it is empty. *)

Parameter valid_pointer: forall (m: mem) (ofs: Z), bool.

Axiom valid_pointer_live_perm:
  forall m ofs,
  valid_pointer m ofs = true <-> perm m ofs Live.
Axiom valid_pointer_valid_access:
  forall m ofs,
  valid_pointer m ofs = true <-> valid_access m Mint8unsigned ofs.

(** C allows pointers one past the last element of an array.  These are not
  valid according to the previously defined [valid_pointer]. The property
  [weak_valid_pointer m b ofs] holds if address [b, ofs] is a valid pointer
  in [m], or a pointer one past a valid block in [m].  *)

Definition weak_valid_pointer (m: mem) (ofs: Z) :=
  valid_pointer m ofs || valid_pointer m (ofs - 1).

Axiom weak_valid_pointer_spec:
  forall m ofs,
  weak_valid_pointer m ofs = true <->
    valid_pointer m ofs = true \/ valid_pointer m (ofs - 1) = true.
Axiom valid_pointer_implies:
  forall m ofs,
  valid_pointer m ofs = true -> weak_valid_pointer m ofs = true.

(** * Properties of the memory operations *)

(** ** Properties of the initial memory state. *)

Axiom perm_empty: forall ofs, ~ perm empty ofs Live.
Axiom valid_access_empty:
  forall chunk ofs, ~valid_access empty chunk ofs.

(** ** Properties of [load]. *)

(** A load succeeds if the access is allowed *)
Axiom allowed_access_load:
  forall m chunk ofs,
    allowed_access m chunk ofs ->
    exists v, load chunk m ofs = Some v.
(* Unclear whether disallowed accesses prevent loads. *)
(*Axiom _access_load_md:
  forall m chunk b ofs,
  allowed_access m chunk b ofs ->
  exists v, load chunk m b ofs = Some v.*)

(** The value returned by [load] belongs to the type of the memory quantity
  accessed: [Vundef], [Vint] or [Vptr] for an integer quantity,
  [Vundef] or [Vfloat] for a float quantity. *)
Axiom load_type:
  forall m chunk ofs v t,
  load chunk m ofs = Some (v,t) ->
  Val.has_type v (type_of_chunk chunk).

Axiom load_rettype:
  forall m chunk ofs v t,
  load chunk m ofs = Some (v,t) ->
  Val.has_rettype v (rettype_of_chunk chunk).

(** For a small integer or float type, the value returned by [load]
  is invariant under the corresponding cast. *)
Axiom load_cast:
  forall m chunk ofs v t,
  load chunk m ofs = Some (v,t) ->
  match chunk with
  | Mint8signed => v = Val.sign_ext 8 v
  | Mint8unsigned => v = Val.zero_ext 8 v
  | Mint16signed => v = Val.sign_ext 16 v
  | Mint16unsigned => v = Val.zero_ext 16 v
  | _ => True
  end.

Axiom load_int8_signed_unsigned:
  forall m ofs,
    load Mint8signed m ofs = opt_atom_map (Val.sign_ext 8) (load Mint8unsigned m ofs).

Axiom load_int16_signed_unsigned:
  forall m ofs,
    load Mint16signed m ofs = opt_atom_map (Val.sign_ext 16) (load Mint16unsigned m ofs).

(** ** Properties of [loadbytes]. *)

(** [loadbytes] definitely succeeds if we have read permissions on the accessed
    memory area. *)

Axiom range_perm_loadbytes_live:
  forall m ofs len,
  range_perm m ofs (ofs + len) Live ->
  exists bytes, loadbytes m ofs len = Some bytes.
Axiom range_perm_loadbytes_md:
  forall m ofs len,
  range_perm m ofs (ofs + len) MostlyDead ->
  exists bytes, loadbytes m ofs len = Some bytes.

(** If [loadbytes] succeeds, the corresponding [load] succeeds and
  returns a value that is determined by the
  bytes read by [loadbytes]. *)
Axiom loadbytes_load:
  forall chunk m ofs bytes,
  loadbytes m ofs (size_chunk chunk) = Some bytes ->
  (align_chunk chunk | ofs) ->
  load chunk m ofs = Some(decode_val chunk bytes).

(** Conversely, if [load] returns a value, the corresponding
  [loadbytes] succeeds and returns a list of bytes which decodes into the
  result of [load]. *)
Axiom load_loadbytes:
  forall chunk m ofs v,
  load chunk m ofs = Some v ->
  exists bytes, loadbytes m ofs (size_chunk chunk) = Some bytes
             /\ v = decode_val chunk bytes.

(** [loadbytes] returns a list of length [n] (the number of bytes read). *)
Axiom loadbytes_length:
  forall m ofs n bytes,
  loadbytes m ofs n = Some bytes ->
  length bytes = Z.to_nat n.

Axiom loadbytes_empty:
  forall m ofs n,
  n <= 0 -> loadbytes m ofs n = Some nil.

(** Composing or decomposing [loadbytes] operations at adjacent addresses. *)
Axiom loadbytes_concat:
  forall m ofs n1 n2 bytes1 bytes2,
    loadbytes m ofs n1 = Some bytes1 ->
    loadbytes m (ofs + n1) n2 = Some bytes2 ->
    n1 >= 0 -> n2 >= 0 ->
    loadbytes m ofs (n1 + n2) = Some(bytes1 ++ bytes2).
Axiom loadbytes_split:
  forall m ofs n1 n2 bytes,
    loadbytes m ofs (n1 + n2) = Some bytes ->
    n1 >= 0 -> n2 >= 0 ->
    exists bytes1, exists bytes2,
      loadbytes m ofs n1 = Some bytes1
      /\ loadbytes m (ofs + n1) n2 = Some bytes2
      /\ bytes = bytes1 ++ bytes2.

(** ** Properties of [store]. *)

(** [store] preserves block validity, permissions, access validity, and bounds.
  Moreover, a [store] succeeds if and only if the corresponding access is allowed. *)

Axiom store_valid_block_1:
  forall chunk m1 ofs v vt lts m2, store chunk m1 ofs (v,vt) lts = Some m2 ->
  forall ofs', valid_addr m1 ofs' -> valid_addr m2 ofs'.
Axiom store_valid_block_2:
  forall chunk m1 ofs v vt lts m2, store chunk m1 ofs (v,vt) lts = Some m2 ->
  forall ofs', valid_addr m2 ofs' -> valid_addr m1 ofs'.

Axiom perm_store_1:
  forall chunk m1 ofs v vt lts m2, store chunk m1 ofs (v,vt) lts = Some m2 ->
  forall ofs' p, perm m1 ofs' p -> perm m2 ofs' p.
Axiom perm_store_2:
  forall chunk m1 ofs v vt lts m2, store chunk m1 ofs (v,vt) lts = Some m2 ->
  forall ofs' p, perm m2 ofs' p -> perm m1 ofs' p.

Axiom allowed_access_store:
  forall m1 chunk ofs v vt lts,
  allowed_access m1 chunk ofs ->
  { m2: mem | store chunk m1 ofs (v,vt) lts = Some m2 }.
Axiom disallowed_access_store:
  forall m1 chunk ofs v vt lts,
  ~ allowed_access m1 chunk ofs ->
  store chunk m1 ofs (v,vt) lts = None.
Axiom store_valid_access_1:
  forall chunk m1 ofs v vt lts m2, store chunk m1 ofs (v,vt) lts = Some m2 ->
  forall chunk' ofs',
  valid_access m1 chunk' ofs' -> valid_access m2 chunk' ofs'.
Axiom store_valid_access_2:
  forall chunk m1 ofs v vt lts m2, store chunk m1 ofs (v,vt) lts = Some m2 ->
  forall chunk' ofs',
  valid_access m2 chunk' ofs' -> valid_access m1 chunk' ofs'.

(** Load-store properties. *)

Axiom load_store_similar:
  forall chunk m1 ofs v vt lts m2, store chunk m1 ofs (v,vt) lts = Some m2 ->
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  exists v' t, load chunk' m2 ofs = Some (v',t) /\ decode_encode_val v chunk chunk' v'.

Axiom load_store_same:
  forall chunk m1 ofs v vt lts m2, store chunk m1 ofs (v,vt) lts = Some m2 ->
  load chunk m2 ofs = Some (Val.load_result chunk v, vt).

Axiom load_store_other:
  forall chunk m1 ofs v vt lts m2, store chunk m1 ofs (v,vt) lts = Some m2 ->
  forall chunk' ofs',
  ofs' + size_chunk chunk' <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  load chunk' m2 ofs' = load chunk' m1 ofs'.

(** Integrity of pointer values. *)

Definition compat_pointer_chunks (chunk1 chunk2: memory_chunk) : Prop :=
  match chunk1, chunk2 with
  | (Mint32 | Many32), (Mint32 | Many32) => True
  | (Mint64 | Many64), (Mint64 | Many64) => True
  | _, _ => False
  end.

Axiom load_store_pointer_overlap:
  forall chunk m1 ofs v_v_o m2 chunk' ofs' v pt lts,
  store chunk m1 ofs (Vint v_v_o, pt) lts = Some m2 ->
  load chunk' m2 ofs' = Some v ->
  ofs' <> ofs ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  v = (Vundef, def_tag).
Axiom load_store_pointer_mismatch:
  forall chunk m1 ofs v_v_o m2 chunk' v pt lts,
  store chunk m1 ofs (Vint v_v_o, pt) lts = Some m2 ->
  load chunk' m2 ofs = Some v ->
  ~compat_pointer_chunks chunk chunk' ->
  v = (Vundef, def_tag).
Axiom load_pointer_store:
  forall chunk m1 ofs v pt lts m2 chunk' ofs' v_v_o pt',
  store chunk m1 ofs (v,pt) lts = Some m2 ->
  load chunk' m2 ofs' = Some(Vint v_v_o, pt') ->
  (v = Vint v_v_o /\ compat_pointer_chunks chunk chunk' /\ ofs' = ofs)
  \/ (ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk chunk <= ofs').

(** Load-store properties for [loadbytes]. *)

Axiom loadbytes_store_same:
  forall chunk m1 ofs v vt lts m2, store chunk m1 ofs (v,vt) lts = Some m2 ->
  loadbytes m2 ofs (size_chunk chunk) = Some(encode_val chunk (v,vt)).
Axiom loadbytes_store_other:
  forall chunk m1 ofs v vt lts m2, store chunk m1 ofs (v,vt) lts = Some m2 ->
  forall ofs' n,
    n <= 0 \/ ofs' + n <= ofs \/ ofs + size_chunk chunk <= ofs' ->
    loadbytes m2 ofs' n = loadbytes m1 ofs' n.

(** [store] is insensitive to the signedness or the high bits of
  small integer quantities. *)

Axiom store_signed_unsigned_8:
  forall m ofs v vt lts,
  store Mint8signed m ofs (v,vt) lts = store Mint8unsigned m ofs (v,vt) lts.
Axiom store_signed_unsigned_16:
  forall m ofs v vt lts,
  store Mint16signed m ofs (v,vt) lts = store Mint16unsigned m ofs (v,vt) lts.
Axiom store_int8_zero_ext:
  forall m ofs n vt lts,
  store Mint8unsigned m ofs (Vint (Int.zero_ext 8 n), vt) lts =
  store Mint8unsigned m ofs (Vint n, vt) lts.
Axiom store_int8_sign_ext:
  forall m ofs n vt lts,
  store Mint8signed m ofs (Vint (Int.sign_ext 8 n), vt) lts =
  store Mint8signed m ofs (Vint n, vt) lts.
Axiom store_int16_zero_ext:
  forall m ofs n vt lts,
  store Mint16unsigned m ofs (Vint (Int.zero_ext 16 n), vt) lts =
  store Mint16unsigned m ofs (Vint n, vt) lts.
Axiom store_int16_sign_ext:
  forall m ofs n vt lts,
  store Mint16signed m ofs (Vint (Int.sign_ext 16 n), vt) lts =
  store Mint16signed m ofs (Vint n, vt) lts.

(** ** Properties of [storebytes]. *)

(** [storebytes] preserves block validity, permissions, access validity, and bounds.
  Moreover, a [storebytes] succeeds if and only if we have write permissions
  on the addressed memory area. *)

Axiom perm_storebytes_1:
  forall m1 ofs bytes ltags m2, storebytes m1 ofs bytes ltags = Some m2 ->
  forall ofs' p, perm m1 ofs' p -> perm m2 ofs' p.
Axiom perm_storebytes_2:
  forall m1 ofs bytes ltags m2, storebytes m1 ofs bytes ltags = Some m2 ->
  forall ofs' p, perm m2 ofs' p -> perm m1 ofs' p.
Axiom storebytes_valid_access_1:
  forall m1 ofs bytes ltags m2, storebytes m1 ofs bytes ltags = Some m2 ->
  forall chunk' ofs',
  valid_access m1 chunk' ofs' -> valid_access m2 chunk' ofs'.
Axiom storebytes_valid_access_2:
  forall m1 ofs bytes ltags m2, storebytes m1 ofs bytes ltags = Some m2 ->
  forall chunk' ofs',
  valid_access m2 chunk' ofs' -> valid_access m1 chunk' ofs'.
Axiom storebytes_allowed_access_1:
  forall m1 ofs bytes ltags m2, storebytes m1 ofs bytes ltags = Some m2 ->
  forall chunk' ofs',
  allowed_access m1 chunk' ofs' -> allowed_access m2 chunk' ofs'.
Axiom storebytes_allowed_access_2:
  forall m1 ofs bytes ltags m2, storebytes m1 ofs bytes ltags = Some m2 ->
  forall chunk' ofs',
  allowed_access m2 chunk' ofs' -> allowed_access m1 chunk' ofs'.
Axiom storebytes_valid_block_1:
  forall m1 ofs bytes ltags m2, storebytes m1 ofs bytes ltags = Some m2 ->
  forall ofs', valid_addr m1 ofs' -> valid_addr m2 ofs'.
Axiom storebytes_valid_block_2:
  forall m1 ofs bytes ltags m2, storebytes m1 ofs bytes ltags = Some m2 ->
  forall ofs', valid_addr m2 ofs' -> valid_addr m1 ofs'.

(** Connections between [store] and [storebytes]. *)

Axiom storebytes_store:
  forall m1 ofs chunk v vt lts m2,
  storebytes m1 ofs (encode_val chunk (v,vt)) lts = Some m2 ->
  (align_chunk chunk | ofs) ->
  store chunk m1 ofs (v,vt) lts = Some m2.

(** Load-store properties. *)

Axiom loadbytes_storebytes_same:
  forall m1 ofs bytes lts m2, storebytes m1 ofs bytes lts = Some m2 ->
  loadbytes m2 ofs (Z.of_nat (length bytes)) = Some bytes.
Axiom loadbytes_storebytes_other:
  forall m1 ofs bytes lts m2, storebytes m1 ofs bytes lts = Some m2 ->
  forall ofs' len,
    len >= 0 ->
    ofs' + len <= ofs
    \/ ofs + Z.of_nat (length bytes) <= ofs' ->
    loadbytes m2 ofs' len = loadbytes m1 ofs' len.
Axiom load_storebytes_other:
  forall m1 ofs bytes lts m2, storebytes m1 ofs bytes lts = Some m2 ->
  forall chunk ofs',
    ofs' + size_chunk chunk <= ofs
    \/ ofs + Z.of_nat (length bytes) <= ofs' ->
    load chunk m2 ofs' = load chunk m1 ofs'.

(** Composing or decomposing [storebytes] operations at adjacent addresses. *)

Axiom storebytes_concat:
  forall m ofs bytes1 lts1 m1 bytes2 lts2 m2,
  storebytes m ofs bytes1 lts1 = Some m1 ->
  storebytes m1 (ofs + Z.of_nat(length bytes1)) bytes2 lts2 = Some m2 ->
  storebytes m ofs (bytes1 ++ bytes2) (lts1 ++ lts2) = Some m2.
Axiom storebytes_split:
  forall m ofs bytes1 bytes2 lts1 lts2 m2,
  storebytes m ofs (bytes1 ++ bytes2) (lts1 ++ lts2) = Some m2 ->
  exists m1,
     storebytes m ofs bytes1 lts1 = Some m1
  /\ storebytes m1 (ofs + Z.of_nat(length bytes1)) bytes2 lts2 = Some m2.

(** ** Properties of [alloc]. *)

(** Effect of [alloc] on block validity. *)

Axiom valid_block_alloc:
  forall m1 lo1 lo2 hi1 hi2 m2, alloc m1 lo1 hi1 = Some (m2, lo2, hi2) ->
  forall ofs, valid_addr m1 ofs -> valid_addr m2 ofs.

Axiom valid_new_block:
  forall m1 lo1 lo2 hi1 hi2 m2, alloc m1 lo1 hi1 = Some (m2, lo2, hi2) ->
  forall ofs, lo2 <= ofs -> ofs < hi2 -> valid_addr m2 ofs.
Axiom valid_block_alloc_inv:
  forall m1 lo1 lo2 hi1 hi2 m2, alloc m1 lo1 hi1 = Some (m2, lo2, hi2) ->
  forall ofs, valid_addr m2 ofs -> (lo2 <= ofs /\ ofs < hi2) \/ valid_addr m1 ofs.

(** Effect of [alloc] on permissions. *)

(*Axiom perm_alloc_1:
  forall m1 lo1 lo2 hi1 hi2 m2, alloc m1 lo1 hi1 = Some (m2, lo2, hi2) ->
  forall ofs p, perm m1 ofs p -> perm m2 ofs p.
Axiom perm_alloc_2:
  forall m1 lo1 lo2 hi1 hi2 m2 b, alloc m1 lo1 hi1 = Some (m2, lo2, hi2) ->
  forall ofs, lo2 <= ofs < hi2 -> perm m2 ofs Live.
Axiom perm_alloc_inv:
  forall m1 lo1 lo2 hi1 hi2 m2, alloc m1 lo1 hi1 = Some (m2, lo2, hi2) ->
  forall ofs p,
  perm m2 ofs p ->
  lo2 <= ofs < hi2 \/ perm m1 ofs p.

(** Effect of [alloc] on access validity. *)

Axiom valid_access_alloc_other:
  forall m1 lo1 lo2 hi1 hi2 m2, alloc m1 lo1 hi1 = Some (m2, lo2, hi2) ->
  forall chunk ofs,
  valid_access m1 chunk ofs ->
  valid_access m2 chunk ofs.
Axiom valid_access_alloc_same:
  forall m1 lo1 lo2 hi1 hi2 m2, alloc m1 lo1 hi1 = Some (m2, lo2, hi2) ->
  forall chunk ofs,
  lo2 <= ofs -> ofs + size_chunk chunk <= hi2 -> (align_chunk chunk | ofs) ->
  valid_access m2 chunk (nextblock m1) ofs.
Axiom valid_access_alloc_inv:
  forall m1 lo1 lo2 hi1 hi2 m2 b, alloc m1 lo1 hi1 = Some (m2, lo2, hi2) ->
  forall chunk ofs,
  valid_access m2 chunk ofs ->
  if eq_block b
  then lo2 <= ofs /\ ofs + size_chunk chunk <= hi2 /\ (align_chunk chunk | ofs)
  else valid_access m1 chunk ofs.

(** Load-alloc properties. *)

Axiom load_alloc_unchanged:
  forall m1 lo1 lo2 hi1 hi2 m2, alloc m1 lo1 hi1 = Some (m2, lo2, hi2) ->
  forall chunk ofs,
  valid_block m1 ->
  load chunk m2 ofs = load chunk m1 ofs.
Axiom load_alloc_other:
  forall m1 lo1 lo2 hi1 hi2 m2, alloc m1 lo1 hi1 = Some (m2, lo2, hi2) ->
  forall chunk ofs v,
  load chunk m1 ofs = Some v ->
  load chunk m2 ofs = Some v.
Axiom load_alloc_same:
  forall m1 lo1 lo2 hi1 hi2 m2 b, alloc m1 lo1 hi1 = Some (m2, lo2, hi2) ->
  forall chunk ofs v,
  load chunk m2 ofs = Some v ->
  v = Vundef.
Axiom load_alloc_same':
  forall m1 lo1 lo2 hi1 hi2 m2, alloc m1 lo1 hi1 = Some (m2, lo2, hi2) ->
  forall chunk ofs,
  lo2 <= ofs -> ofs + size_chunk chunk <= hi2 -> (align_chunk chunk | ofs) ->
  load chunk m2 (nextblock m1) ofs = Some Vundef.
*)
(** ** Properties of [free]. *)

(** [free] succeeds if and only if the correspond range of addresses
  has [Live] current permission. *)

Axiom range_perm_free:
  forall m1 lo hi,
    range_perm m1 lo hi Live ->
    { m2: mem | free m1 lo hi = Some m2 }.
Axiom free_range_perm:
  forall m1 lo hi m2, free m1 lo hi = Some m2 ->
  range_perm m1 lo hi Live.

(** Block validity is preserved by [free]. *)

Axiom valid_block_free_1:
  forall m1 lo hi m2, free m1 lo hi = Some m2 ->
  forall ofs, (lo > ofs \/ hi <= ofs) -> valid_addr m1 ofs -> valid_addr m2 ofs.
Axiom valid_block_free_2:
  forall m1 lo hi m2, free m1 lo hi = Some m2 ->
  forall ofs, valid_addr m2 ofs -> valid_addr m1 ofs.

(** Effect of [free] on permissions. *)
(*
Axiom` perm_free_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall ofs p,
  <> bf \/ ofs < lo \/ hi <= ofs ->
  perm m1 ofs p ->
  perm m2 ofs p.
Axiom perm_free_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall ofs, lo <= ofs < hi -> perm m2 bf ofs MostlyDead.
Axiom perm_free_3:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall ofs p,
  perm m2 ofs p -> perm m1 ofs p.

(** Effect of [free] on access validity. *)

Axiom valid_access_free_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk ofs,
  valid_access m1 chunk ofs ->
  <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  valid_access m2 chunk ofs.
Axiom valid_access_free_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk ofs,
  lo < hi -> ofs + size_chunk chunk > lo -> ofs < hi ->
  ~(valid_access m2 chunk bf ofs).
Axiom valid_access_free_inv_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk ofs,
  valid_access m2 chunk ofs ->
  valid_access m1 chunk ofs.
Axiom valid_access_free_inv_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk ofs,
  valid_access m2 chunk bf ofs ->
  lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs.

(** Load-free properties *)

Axiom load_free:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk ofs,
  <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  load chunk m2 ofs = load chunk m1 ofs.

(** * Relating two memory states. *)

(** ** Memory extensions *)

(**  A store [m2] extends a store [m1] if [m2] can be obtained from [m1]
  by relaxing the permissions of [m1] (for instance, allocating larger
  blocks) and replacing some of the [Vundef] values stored in [m1] by
  more defined values stored in [m2] at the same addresses. *)

Parameter extends: mem -> mem -> Prop.

Axiom extends_refl:
  forall m, extends m m.

Axiom load_extends:
  forall chunk m1 m2 ofs v1,
  extends m1 m2 ->
  load chunk m1 ofs = Some v1 ->
  exists v2, load chunk m2 ofs = Some v2 /\ Val.lessdef v1 v2.

Axiom loadv_extends:
  forall chunk m1 m2 addr1 addr2 v1,
  extends m1 m2 ->
  loadv chunk m1 addr1 = Some v1 ->
  Val.lessdef addr1 addr2 ->
  exists v2, loadv chunk m2 addr2 = Some v2 /\ Val.lessdef v1 v2.

Axiom loadbytes_extends:
  forall m1 m2 ofs len bytes1,
  extends m1 m2 ->
  loadbytes m1 ofs len = Some bytes1 ->
  exists bytes2, loadbytes m2 ofs len = Some bytes2
              /\ list_forall2 memval_lessdef bytes1 bytes2.

Axiom store_within_extends:
  forall chunk m1 m2 ofs v1 m1' v2,
  extends m1 m2 ->
  store chunk m1 ofs v1 = Some m1' ->
  Val.lessdef v1 v2 ->
  exists m2',
     store chunk m2 ofs v2 = Some m2'
  /\ extends m1' m2'.

Axiom store_outside_extends:
  forall chunk m1 m2 ofs v m2',
  extends m1 m2 ->
  store chunk m2 ofs v = Some m2' ->
  (forall ofs', perm m1 ofs' Live -> ofs <= ofs' < ofs + size_chunk chunk -> False) ->
  extends m1 m2'.

Axiom storev_extends:
  forall chunk m1 m2 addr1 v1 m1' addr2 v2,
  extends m1 m2 ->
  storev chunk m1 addr1 v1 = Some m1' ->
  Val.lessdef addr1 addr2 ->
  Val.lessdef v1 v2 ->
  exists m2',
     storev chunk m2 addr2 v2 = Some m2'
  /\ extends m1' m2'.

Axiom storebytes_within_extends:
  forall m1 m2 ofs bytes1 m1' bytes2,
  extends m1 m2 ->
  storebytes m1 ofs bytes1 = Some m1' ->
  list_forall2 memval_lessdef bytes1 bytes2 ->
  exists m2',
     storebytes m2 ofs bytes2 = Some m2'
  /\ extends m1' m2'.

Axiom storebytes_outside_extends:
  forall m1 m2 ofs bytes2 m2',
  extends m1 m2 ->
  storebytes m2 ofs bytes2 = Some m2' ->
  (forall ofs', perm m1 ofs' Live -> ofs <= ofs' < ofs + Z.of_nat (length bytes2) -> False) ->
  extends m1 m2'.

Axiom alloc_extends:
  forall m1 m2 lo1 lo1' hi1 hi1' m1' lo2 lo2' hi2 hi2',
  extends m1 m2 ->
  alloc m1 lo1 hi1 = Some (m1', lo1', hi1') ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists m2',
     alloc m2 lo2 hi2 = Some (m2', lo2', hi2')
  /\ extends m1' m2'.

Axiom free_left_extends:
  forall m1 m2 lo hi m1',
  extends m1 m2 ->
  free m1 lo hi = Some m1' ->
  extends m1' m2.

Axiom free_right_extends:
  forall m1 m2 lo hi m2',
  extends m1 m2 ->
  free m2 lo hi = Some m2' ->
  (forall ofs p, perm m1 ofs p -> lo <= ofs < hi -> False) ->
  extends m1 m2'.

Axiom free_parallel_extends:
  forall m1 m2 lo hi m1',
  extends m1 m2 ->
  free m1 lo hi = Some m1' ->
  exists m2',
     free m2 lo hi = Some m2'
  /\ extends m1' m2'.

Axiom valid_block_extends:
  forall m1 m2 b,
  extends m1 m2 ->
  (valid_block m1 <-> valid_block m2 b).
Axiom perm_extends:
  forall m1 m2 ofs p,
  extends m1 m2 -> perm m1 ofs p -> perm m2 ofs p.
Axiom valid_access_extends:
  forall m1 m2 chunk ofs,
  extends m1 m2 -> valid_access m1 chunk ofs -> valid_access m2 chunk ofs.
Axiom valid_pointer_extends:
  forall m1 m2 ofs,
  extends m1 m2 -> valid_pointer m1 ofs = true -> valid_pointer m2 ofs = true.
Axiom weak_valid_pointer_extends:
  forall m1 m2 ofs,
  extends m1 m2 ->
  weak_valid_pointer m1 ofs = true -> weak_valid_pointer m2 ofs = true.*)

End MEM.
