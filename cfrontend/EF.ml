open Ctypes

let extern_functions = [
        (((AST.EF_malloc,
        Tcons(Tlong(Unsigned, noattr),Tnil)),
        Tpointer(Tvoid,noattr)),
        AST.cc_default);
        
        (((AST.EF_free,
        Tcons(Tpointer(Tvoid, noattr),Tnil)),
        Tvoid),
        AST.cc_default);

        (((AST.EF_external(Camlcoq.coqstring_of_camlstring "printf",
                                {AST.sig_args = [AST.Tlong];
                                 AST.sig_res = AST.Tret(AST.Tint);
                                 AST.sig_cc = AST.cc_default;}),
        Tcons(Tint(I8,Signed,noattr),Tnil)),
        Tint(I32,Signed,noattr)),
        AST.cc_default);

        (((AST.EF_external(Camlcoq.coqstring_of_camlstring "fgets",
                                {AST.sig_args = [AST.Tlong; AST.Tint];
                                 AST.sig_res = AST.Tret(AST.Tlong);
                                 AST.sig_cc = AST.cc_default;}),
        Tcons(Tlong(Signed,noattr),Tcons(Tint(I8,Signed,noattr),Tnil))),
        Tlong(Signed,noattr)),
        AST.cc_default);
]

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
