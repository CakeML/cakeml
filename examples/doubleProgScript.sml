(*
  Examples on the topic of doubling a number.
*)
open preamble semanticPrimitivesTheory
     ml_translatorTheory ml_translatorLib ml_progLib cfLib basisFunctionsLib
     basisProgTheory

val _ = new_theory "doubleProg";

val _ = translation_extends "basisProg";

fun basis_st () = get_ml_prog_state ()

(**********)

val double = process_topdecs `
    fun double x = if x = 0 then 0 else double (x - 1) + 2;
`;

val _ = append_prog double;

Theorem double_spec:
     ∀x x_v. NUM x x_v
        ⇒ app (p:'ffi ffi_proj) ^(fetch_v "double" (basis_st())) [x_v]
        emp (POSTv v. &(NUM (2 * x) v))
Proof
    Induct_on `x` >>
    xcf "double" (basis_st())
    >- (xlet_auto
        >- xsimpl
        >> xif >> fs[BOOL_def] >>
           xret >> xsimpl)
    >- (
        xlet_auto
        >- xsimpl
        >> xif >>
           fs[BOOL_def] >>
           xlet_auto
           >- xsimpl
           >> xlet_auto
                >- xsimpl
                >> xapp >>
                   xsimpl >>
                   fs[NUM_def, INT_def] >>
                   fs[integerTheory.INT_ADD_CALCULATE]
        )
QED

(**********)

val double_tail_rec = process_topdecs `
    fun double_tail_rec x = if x = 0 then 0 else
        let fun aux n carry =
            if n = 0 then carry else
                aux (n - 1) (carry + 2)
        in aux x 0 end;
`;

val _ = append_prog double_tail_rec;

Theorem double_tail_rec_spec:
     ∀x x_v. NUM x x_v
        ⇒ app (p:'ffi ffi_proj) ^(fetch_v "double_tail_rec" (basis_st())) [x_v]
        emp (POSTv v. &(NUM (2 * x) v))
Proof
    xcf "double_tail_rec" (basis_st()) >>
    xlet_auto
        >- xsimpl >>
    xif >> fs[BOOL_def]
    >- (xlit >> xsimpl)
    >>  reverse (xfun_spec `aux`
        `∀ n n_v carry carry_v .
            NUM n n_v ∧
            NUM carry carry_v
          ⇒ app p aux [n_v; carry_v]
            emp (POSTv v . &(NUM (2 * n + carry) v))`
        )
        >- (
            xapp >>
            xsimpl >>
            qexists_tac `x` >> fs[]
            )
        >>  Induct >> rw[] >>
            last_x_assum xapp_spec
            >- (
                xlet_auto
                    >- xsimpl >>
                xif >> fs[BOOL_def] >>
                xvar >> xsimpl
                )
            >>  xlet_auto
                    >- xsimpl >>
                xif >> fs[BOOL_def] >>
                xlet_auto
                    >- xsimpl >>
                xlet_auto
                    >- xsimpl >>
                last_x_assum xapp_spec >>
                xsimpl >>
                qexists_tac `carry + 2` >> fs[] >>
                fs[ADD1] >>
                fs[NUM_def, INT_def, INT_OF_NUM_SUBS]
QED

(**********)

val double_ref = process_topdecs `
    fun double_ref x =
        if !x = 0 then (Ref 0) else
            (
                x := (!x - 1);
                (let val result = (double_ref x) in
                    (result := !result + 2; result)
                 end)
            );
`;

val _ = append_prog double_ref;

Theorem double_ref_spec:
     ∀ inp inp_v inp_ref ffi_p .
        NUM inp inp_v
      ⇒ app (ffi_p:'ffi ffi_proj) ^(fetch_v "double_ref" (basis_st())) [inp_ref]
        (inp_ref ~~> inp_v)
        (POSTv ret_ref .
            (SEP_EXISTS inp0_v .
                (inp_ref ~~> inp0_v) * &(NUM 0 inp0_v)) *
            (SEP_EXISTS ret_v .
                (ret_ref ~~> ret_v) * &(NUM (2 * inp) ret_v))
        )
Proof
    Induct_on `inp` >>
    xcf "double_ref" (basis_st())
    >- (xlet_auto
        >- xsimpl
        >> rveq >> xlet_auto
           >- xsimpl
           >> xif >> fs[BOOL_def] >>
                xref >> xsimpl)
    >>
        (*
        let a = !x in
        let b = (a = 0) in
        if b then (ref 0) else
            let c = !x in
            let d = c - 1 in
                x := d; let result = double_ref x in
                    let e = !result in
                    let f = e + 2 in
                    (result := f; result)
        *)
        fs[ADD1] >>
        xlet_auto (* a *)
            >- xsimpl
        >> rveq >> xlet_auto (* b*)
            >- xsimpl
        >> xif >> fs[BOOL_def] >> xlet_auto (* c *)
            >- xsimpl
        >> rveq >> xlet_auto (* d *)
            >- xsimpl
        >> xlet_auto (* x := d; *)
            >- xsimpl
        >> last_x_assum imp_res_tac >>
           xlet_auto (* result *)
            >- xsimpl
        >> xlet_auto (* e *)
            >- xsimpl
        >> rveq >> xlet_auto (* f *)
            >- xsimpl
        >> xlet_auto (* result := f; *)
            >- xsimpl
        >> xvar >> xsimpl >>
           fs[NUM_def, INT_def]
QED

(**********)

val double_ref_same = process_topdecs `
    fun double_ref_same x =
        if !x = 0 then x else
            (x := (!x - 1); x := (!(double_ref_same x) + 2); x);
`;

val _ = append_prog double_ref_same;

Theorem double_ref_same_spec:
     ∀ inp inp_v inp_ref ffi_p .
        NUM inp inp_v
      ⇒ app (ffi_p:'ffi ffi_proj)
        ^(fetch_v "double_ref_same" (basis_st())) [inp_ref]
        (inp_ref ~~> inp_v)
        (POSTv ret_ref .
            (SEP_EXISTS ret_v .
                (ret_ref ~~> ret_v) *
               &(NUM (2 * inp) ret_v ∧
                 ret_ref = inp_ref)
            )
        )
Proof
    Induct_on `inp` >>
    xcf "double_ref_same" (basis_st())
    >- (
        xlet_auto
        >- xsimpl
        >> rveq >> xlet_auto
           >- xsimpl
           >> xif >> fs[BOOL_def] >>
                xvar >> xsimpl)
    >>
        (*
        let a = !x in
        let b = (a = 0) in
        if b then x else
            let c = !x in  (NB a = c)
            let d = c - 1 in
                x := d;
                let e = double_ref_same x in
                let f = !e in
                let g = f + 2 in
                    x := g; x
        *)
        fs[ADD1] >>
        xlet_auto (* a *)
            >- xsimpl
        >> rveq >> xlet_auto (* b*)
            >- xsimpl
        >> xif >> fs[BOOL_def] >> xlet_auto (* c *)
            >- xsimpl
        >> rveq >> xlet_auto (* d *)
            >- xsimpl
        >> xlet_auto (* x := d; *)
            >- xsimpl
        >> last_x_assum imp_res_tac >>
           xlet_auto (* e *)
            >- xsimpl
        >> rveq >> xlet_auto (* f *)
            >- xsimpl
        >> rveq >> xlet_auto (* g *)
            >- xsimpl
        >> xlet_auto (* x := g; *)
            >- xsimpl
        >> xvar >> xsimpl >>
            fs[NUM_def, INT_def]
QED

val _ = export_theory();
