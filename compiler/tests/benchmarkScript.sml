open HolKernel boolLib bossLib lcsymtacs arithmeticTheory relationTheory pairTheory prim_recTheory (* ml_translatorLib *)

val _ = new_theory"benchmark"

val _ = intLib.deprecate_int()

(*
val fib_def = mlDefine`
  (fib 0 = 1) ∧
  (fib (SUC 0) = 1) ∧
  (fib n = fib (n - 1) + fib (n - 2))`

val fact_def = mlDefine`
  (fact 0 = 1) ∧
  (fact (SUC n) = (SUC n) * fact n)`
*)

(*
val m1_def = Define`
  m1 (x,y,z) = if x:num ≤ y then 0:num else 1`
val m2_def = Define`
  m2 (x,y,z) = MAX x (MAX y z) - MIN x (MIN y z)`
val m3_def = Define`
  m3 (x,y,z) = x - MIN x (MIN y z)`
val m_def = Define`
  m (x,y,z) = (m1(x,y,z),m2(x,y,z),m3(x,y,z))`
val r_def = Define`
  r = inv_image (prim_rec$< LEX prim_rec$< LEX prim_rec$<) m`

val m2l1 = prove(
``m2 (x-1,y,z) ≤ m2 (x,y,z)``,
srw_tac[][m2_def]
>> srw_tac[][MIN_DEF,MAX_DEF]
>> srw_tac[ARITH_ss][] >>
rpt (pop_assum mp_tac) >>
>> srw_tac[ARITH_ss][] >>
DECIDE_TAC

val th1 = prove(
``x ≤ y ⇒ r (x-1,y,z) (x,y,z)``,
srw_tac[ARITH_ss][r_def,inv_image_def,LEX_DEF,m_def,m1_def] >>
srw_tac[ARITH_ss][m3_def,MIN_DEF,MAX_DEF]

val tak_defn = Hol_defn "tak"`
  tak (x:num) y z = if y < x then
    tak (tak (x-1) y z) (tak (y-1) z x) (tak (z-1) x y)
  else z` (* or y? *)
val tak_tupled_aux_def = definition "tak_tupled_AUX_def"
val (tak_def,tak_ind) = Defn.tprove(tak_defn,
qexists_tac `inv_image (prim_rec$< LEX prim_rec$< LEX prim_rec$<) m` >>
conj_tac >- rw[WF_inv_image,WF_LEX,WF_LESS] >>
conj_tac >- (
  rw[inv_image_def,LEX_DEF,m_def,m1_def] >>
  >- srw_tac[ARITH_ss][]
  >- srw_tac[ARITH_ss][]
  >- srw_tac[ARITH_ss][MIN_DEF,MAX_DEF,m2_def,m3_def] ) >>
conj_tac >- (
  rw[inv_image_def,LEX_DEF,m_def,m1_def]
  >- srw_tac[ARITH_ss][]
  >- srw_tac[ARITH_ss][]
  >- srw_tac[ARITH_ss][m3_def]

val (tak_def,tak_ind) = Defn.tprove(tak_defn,
qexists_tac
`inv_image (prim_rec$< LEX prim_rec$< LEX prim_rec$<)
            (λ(x,y,z). (if x ≤ y then 0 else 1,
                        MAX x (MAX y z) -
                        MIN x (MIN y z),
                        x - MIN x (MIN y z)))` >>
conj_tac >- rw[WF_inv_image,WF_LEX,WF_LESS] >>
conj_tac >- (
  rw[inv_image_def,LEX_DEF]
  >- srw_tac[ARITH_ss][]
  >- srw_tac[ARITH_ss][]
  >- srw_tac[ARITH_ss][MIN_DEF,MAX_DEF] ) >>
conj_tac >- (
  rw[inv_image_def,LEX_DEF]
  >- srw_tac[ARITH_ss][]
  >- srw_tac[ARITH_ss][]
  >- (
    rw[MAX_DEF]
    >- srw_tac[ARITH_ss][]
    >- srw_tac[ARITH_ss][MIN_DEF]
    >- srw_tac[ARITH_ss][]
    >- srw_tac[ARITH_ss][MIN_DEF]
    >- srw_tac[ARITH_ss][]
    >- srw_tac[ARITH_ss][]
    >- srw_tac[ARITH_ss][]
    >- srw_tac[ARITH_ss][]
    >- srw_tac[ARITH_ss][]
    >- srw_tac[ARITH_ss][]
    >- srw_tac[ARITH_ss][]
    >- srw_tac[ARITH_ss][]
    >- srw_tac[ARITH_ss][MIN_DEF]
    >- srw_tac[ARITH_ss][MIN_DEF]
    >- srw_tac[ARITH_ss][]
    >- srw_tac[ARITH_ss][]
    >- (
      rw[MIN_DEF]
      >- srw_tac[ARITH_ss][]
      >- DECIDE_TAC
      >- srw_tac[ARITH_ss][]
      >- srw_tac[ARITH_ss][]
      >- srw_tac[ARITH_ss][]
      >- srw_tac[ARITH_ss][]
      >- srw_tac[ARITH_ss][]
      >- srw_tac[ARITH_ss][]
      >- fsrw_tac[ARITH_ss][]
      >- srw_tac[ARITH_ss][]
      >- fsrw_tac[ARITH_ss][] ) ) ) >>
conj_tac >- (
  rw[inv_image_def,LEX_DEF]
  >- srw_tac[ARITH_ss][]
  >- srw_tac[ARITH_ss][]
  >- srw_tac[ARITH_ss][MIN_DEF,MAX_DEF] ) >>
rpt strip_tac >>
qmatch_abbrev_tac `R (t R (x-1,y,z),t R (y-1,z,x),t R (z-1,x,y)) (x,y,z)` >>
qabbrev_tac `tt = t R` >>
qunabbrev_tac `t` >>
rw[inv_image_def,LEX_DEF,Abbr`R`]
>- srw_tac[ARITH_ss][]
>- srw_tac[ARITH_ss][] >>
rw[MIN_DEF]
>- srw_tac[ARITH_ss][]
>- srw_tac[ARITH_ss][]
>- srw_tac[ARITH_ss][]
>- srw_tac[ARITH_ss][]
>- srw_tac[ARITH_ss][]
>- srw_tac[ARITH_ss][]
>- srw_tac[ARITH_ss][]
>- srw_tac[ARITH_ss][]
>- srw_tac[ARITH_ss][]
>- srw_tac[ARITH_ss][]
>- (
  rw[MAX_DEF]
  >- srw_tac[ARITH_ss][]
  >- srw_tac[ARITH_ss][]
  >- srw_tac[ARITH_ss][]
  >- (
    fsrw_tac[ARITH_ss][NOT_LESS_EQUAL,NOT_LESS] >>
    WFREC_DEF
    rw[PROVE[]``A\/B = ~A==>B``]
    qmatch_abbrev_tac `A \/ B` >>
    Cases_on `A` >> rw[]
    DB.match [] ``a ==> b = ~a \/ b``
    disj1_tac
    conj_tac
    DB.match [] ``~(x:num <= y)``
    ???
    )
>- (
  rw[MAX_DEF]
  >- srw_tac[ARITH_ss][]
  >- srw_tac[ARITH_ss][]
  >- srw_tac[ARITH_ss][]
  >- srw_tac[ARITH_ss][]
  >- srw_tac[ARITH_ss][]
  >- srw_tac[ARITH_ss][]
  >- srw_tac[ARITH_ss][]
  >- ???
  >- ??? )
>- srw_tac[ARITH_ss][]
>- srw_tac[ARITH_ss][]
>- srw_tac[ARITH_ss][]
>- srw_tac[ARITH_ss][]
>- (
  rw[MAX_DEF]
  >- srw_tac[ARITH_ss][]
  >- srw_tac[ARITH_ss][]
  >- srw_tac[ARITH_ss][]
  >- srw_tac[ARITH_ss][]
  >- srw_tac[ARITH_ss][]
  >- ???
  >- srw_tac[ARITH_ss][]
  >- srw_tac[ARITH_ss][]
  >- ??? )
>- (
  srw_tac[ARITH_ss][MAX_DEF]
  >- ???
  >- ??? )
>- srw_tac[ARITH_ss][]
*)

val _ = export_theory()
