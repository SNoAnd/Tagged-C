open Ctypes
open Camlcoq

let malloc_tuple =
        (((AST.EF_malloc,
        Tcons(Tlong(Unsigned, noattr),Tnil)),
        Tpointer(Tvoid,noattr)),
        AST.cc_default)
        
let free_tuple =
        (((AST.EF_free,
        Tcons(Tpointer(Tvoid, noattr),Tnil)),
        Tvoid),
        AST.cc_default)

let printf_tuple =
        (((AST.EF_external(Camlcoq.coqstring_of_camlstring "printf",
                                {AST.sig_args = [AST.Tlong];
                                 AST.sig_res = AST.Tret(AST.Tint);
                                 AST.sig_cc = { AST.cc_vararg = Some(coqint_of_camlint 1l);
                                                AST.cc_unproto = false;
                                                AST.cc_structret = false }}),
        Tcons(Tpointer(Tint(I8,Signed,noattr),noattr),Tnil)),
        Tint(I32,Signed,noattr)),
        AST.cc_default)

let fgets_tuple =
        (((AST.EF_external(Camlcoq.coqstring_of_camlstring "fgets",
                                {AST.sig_args = [AST.Tlong; AST.Tint; AST.Tlong];
                                 AST.sig_res = AST.Tret(AST.Tlong);
                                 AST.sig_cc = AST.cc_default;}),
        Tcons(Tpointer(Tint(I8,Signed,noattr),noattr),
                Tcons(Tint(I32,Signed,noattr),
                        Tcons(Tpointer(Tstruct(intern_string "_IO_FILE",noattr),noattr),Tnil)))),
        Tpointer(Tint(I8,Signed,noattr),noattr)),
        AST.cc_default)

let check_ef id = None
        (*if intern_string "malloc" = id then Some(malloc_tuple) else
        if intern_string "free" = id then Some(free_tuple) else
        if intern_string "printf" = id then Some(printf_tuple) else
        if intern_string "fgets" = id then Some(fgets_tuple) else
        None*)

(** Add declarations for the helper functions
    (for varargs and for int64 arithmetic) *)

(*let helper_functions () = [
    "__compcert_va_int32",
        Tint(I32, Unsigned, noattr),
        [Tpointer(Tvoid, noattr)];
    "__compcert_va_int64",
        Tlong(Unsigned, noattr),
        [Tpointer(Tvoid, noattr)];
    "__compcert_va_float64",
        Tfloat(F64, noattr),
        [Tpointer(Tvoid, noattr)];
    "__compcert_va_composite",
        Tpointer(Tvoid, noattr),
        [Tpointer(Tvoid, noattr); convertIkind (Cutil.size_t_ikind()) noattr];
    "__compcert_i64_dtos",
        Tlong(Signed, noattr),
        [Tfloat(F64, noattr)];
    "__compcert_i64_dtou",
        Tlong(Unsigned, noattr),
        [Tfloat(F64, noattr)];
    "__compcert_i64_stod",
        Tfloat(F64, noattr),
        [Tlong(Signed, noattr)];
    "__compcert_i64_utod",
        Tfloat(F64, noattr),
        [Tlong(Unsigned, noattr)];
    "__compcert_i64_stof",
        Tfloat(F32, noattr),
        [Tlong(Signed, noattr)];
    "__compcert_i64_utof",
        Tfloat(F32, noattr),
        [Tlong(Unsigned, noattr)];
    "__compcert_i64_sdiv",
        Tlong(Signed, noattr),
        [Tlong(Signed, noattr); Tlong(Signed, noattr)];
    "__compcert_i64_udiv",
        Tlong(Unsigned, noattr),
        [Tlong(Unsigned, noattr); Tlong(Unsigned, noattr)];
    "__compcert_i64_smod",
        Tlong(Signed, noattr),
        [Tlong(Signed, noattr); Tlong(Signed, noattr)];
    "__compcert_i64_umod",
        Tlong(Unsigned, noattr),
        [Tlong(Unsigned, noattr); Tlong(Unsigned, noattr)];
    "__compcert_i64_shl",
        Tlong(Signed, noattr),
        [Tlong(Signed, noattr); Tint(I32, Signed, noattr)];
]*)
