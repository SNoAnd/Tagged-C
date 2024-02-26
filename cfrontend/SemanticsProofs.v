Require Import Coqlib Errors Maps.
Require Import Integers Floats Values AST Memory Allocator Builtins Events Globalenvs Tags.
Require Import Ctypes Cop Csyntax Csem.
Require Import Smallstep.
Require Import List. Import ListNotations.
Require Import String.



Module PolicyInsensitivity (Ptr: Pointer) (Pol1: Policy) (Pol2: Policy)
       (M: Memory Ptr) (A: Allocator Ptr).
  Module M1 := M Pol1.
  Module M2 := M Pol2.
  Module A1 := A Pol1 M1.
  Module A2 := A Pol2 M2.
  Module Csem1 := Csem Ptr Pol1 M1 A1.
  Module Csem2 := Csem Ptr Pol2 M2 A2.

  Module PE := ProgEquiv Ptr Pol1 M1 A1
            Ptr2 Pol2 M2 A2.

  
  Variable prog1 : Csem1.Csyntax.program.
  Variable prog2 : Csem2.Csyntax.program.

  Axiom same_prog := program_match prog1 prog2.
  
End PolicyInsensitivity.

  Module Compartmentalization (Ptr: Pointer) (Pol: Policy)
       (M: Memory) (A: Allocator).
  Module Ctop := Ctop Ptr.
  Module Csem := Csem Ptr Pol M A.

  Variable prog : Ctop.program.
  
End Compartmentalization.
