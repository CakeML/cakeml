(**
  Definition of datatype for real-valued polynomials

  We formalize univariate polynomials only. Currently HOL4 only supports
  derivatives of univariate polynomials, and therefore adding
  multivariate polynomials would significantly increase the complexity
  of the project.
  Inspired by and proven equivalent to the definitions of Harrison
**)
open realTheory realLib RealArith bossLib polyTheory;
open renameTheory;
open bitArithLib preambleDandelion;

val _ = new_theory "realPoly";

(**
  We follow the "standard" formalizations used in the HOL family,
  a polynomial p = c_0 * x^0 + c_1 * x^1 + c_2 * x^2 + ...
  is expressed as the list of real numbers [c_0; c_1; c_2; ...]
**)
Type poly = “:real list”

(* Evaluation of a polynomial *)
Definition evalPoly_def:
  evalPoly [] x = 0:real ∧
  evalPoly (c::cs) x = c + (x * evalPoly cs x)
End

(* Normalization; remove trailing zeroes *)
Definition reduce_def:
  reduce []:poly = [] ∧
  reduce (c::cs) =
    (let normalCs = reduce cs in
    if normalCs = [] then
       if c = 0 then [] else [c]
     else c::normalCs)
End

(* Smart constructors for constants and variables *)
Definition cst_def:
  cst (c:real):poly = if c = 0 then [] else [c]
End

Definition var_def:
  var (0:num):poly = [1] ∧
  var (SUC n) = 0::(var n)
End

(** monomial function, shifts polynomial p by n steps by preprending 0's *)
Definition monom_def:
  monom (0:num) (p:poly) = p ∧
  monom (SUC d:num) (p:poly) = [&0] ++ (monom d p)
End

Definition coeff_def:
  coeff (p:poly) n =
  case oEL n p of
  | NONE => 0:real
  | SOME x => x
End

(* Negation, Addition, Subtraction, Multiplication with constants,
polynomial multiplication *)
Definition poly_add_aux_def:
  poly_add_aux [] p2:poly = p2 ∧
  poly_add_aux (c1::cs1) p2 =
    case p2 of
    | [] => (c1::cs1)
    | (c2::cs2) => (c1+c2):: poly_add_aux cs1 cs2
End

Definition poly_add_def:
  poly_add p1 p2 = reduce (poly_add_aux p1 p2)
End

Definition poly_mul_cst_aux_def[nocompute]:
  poly_mul_cst_aux c []:poly = [] ∧
  poly_mul_cst_aux c (c1::cs) = (c * c1) :: poly_mul_cst_aux c cs
End

Theorem poly_mul_cst_aux_comp[compute]:
  poly_mul_cst_aux c p =
  (if p = [] then [] else
    let hdP = HD p; newC = c * hdP in newC :: poly_mul_cst_aux c (TL p))
Proof
  Induct_on ‘p’ >> gs[poly_mul_cst_aux_def]
QED

Definition poly_mul_cst_def[nocompute]:
  poly_mul_cst c p = reduce (poly_mul_cst_aux c p)
End

Theorem poly_mul_cst_comp[compute]:
  poly_mul_cst c p =
    let cmul_p = poly_mul_cst_aux c p in reduce cmul_p
Proof
  gs[poly_mul_cst_def]
QED

Definition poly_neg_def:
  poly_neg p = poly_mul_cst (-1) p
End

Definition poly_sub_def[nocompute]:
  poly_sub p1 p2 = poly_add p1 (poly_neg p2)
End

Theorem poly_sub_comp[compute]:
  poly_sub p1 p2 =
    let p2_neg = poly_mul_cst (-1) p2 in poly_add p1 p2_neg
Proof
  gs[poly_sub_def, poly_neg_def]
QED

Definition poly_mul_def[nocompute]:
  poly_mul [] p2 = [] ∧
  poly_mul (c1::cs1) p2 =
    poly_add (poly_mul_cst c1 p2) (if cs1 = [] then [] else 0::(poly_mul cs1 p2))
End

Theorem poly_mul_comp[compute]:
  poly_mul p1 p2 =
  if p1 = [] then [] else
    let hd_p1 = HD p1;
        mul_cst1 = poly_mul_cst hd_p1 p2;
        remain = if TL p1 = [] then [] else let rec = (poly_mul (TL p1) p2) in 0::rec
    in
      poly_add mul_cst1 remain
Proof
  Induct_on ‘p1’ >> gs[poly_mul_def]
QED

Definition poly_pow_def:
  poly_pow p 0 = [1]:poly ∧
  poly_pow p (SUC n) = poly_mul p (poly_pow p n)
End

Definition derive_aux_def[nocompute]:
  derive_aux n ([]:poly) = [] ∧
  derive_aux n (c::cs) = (&n * c) :: derive_aux (SUC n) cs
End

Theorem derive_aux_comp[compute]:
  derive_aux n p =
  if p = [] then []
  else let hd_elem = HD p;
           hd_deriv = &n * hd_elem;
           rec_res = derive_aux (SUC n) (TL p)
       in
         hd_deriv :: rec_res
Proof
  Induct_on ‘p’ >> gs[derive_aux_def]
QED

Definition derive_def:
  derive (l:poly) = reduce (if l = [] then [] else derive_aux 1 (TL l))
End

Definition deg_def:
  deg(p:poly) = LENGTH (reduce p) - 1
End

val _ = map Parse.overload_on [
    ("--p", Term ‘poly_neg’),
    ("+p", Term ‘poly_add’),
    ("-p", Term ‘poly_sub’),
    ("*p", Term ‘poly_mul’),
    ("*c", Term ‘poly_mul_cst’),
    ("**p", Term ‘poly_pow’)
    ]

val _ = map (uncurry set_fixity)
            [ ("+p", Infix(NONASSOC, 461)),
              ("-p", Infix(NONASSOC, 461)),
              ("*p", Infix(NONASSOC, 470)),
              ("*c", Infix(NONASSOC, 470)),
              ("**p",Infix(NONASSOC, 471))
            ]

Definition zerop_def:
  zerop (p:poly) = (reduce p = [])
End

Theorem reduce_preserving:
  ∀ p.
    evalPoly (reduce p) = evalPoly p
Proof
  Induct_on ‘p’ >> gs[reduce_def, FUN_EQ_THM]
  >> rpt strip_tac >> gs[evalPoly_def]
  >> rename1 ‘c1 :: reduce cs’
  >> ntac 2 (cond_cases_tac >> gs[evalPoly_def])
QED

Theorem cst_reduced:
  ∀ c. reduce (cst c) = cst c
Proof
  rpt strip_tac >> gs[cst_def] >> cond_cases_tac >> gs[reduce_def]
QED

Theorem var_not_empty:
  ∀ n. var n ≠ []
Proof
  strip_tac >> Cases_on ‘n’ >> gs[var_def]
QED

Theorem var_reduced:
  ∀ n.
    reduce (var n) = var n
Proof
  Induct_on ‘n’ >> gs[var_def, reduce_def, var_not_empty]
QED

Theorem reduce_idempotent:
  ∀ p.
    reduce (reduce p) = reduce p
Proof
  Induct_on ‘p’ >> gs[reduce_def]
  >> rpt strip_tac >> cond_cases_tac
  >- (cond_cases_tac >> gs[reduce_def])
  >> gs[reduce_def]
QED

Theorem poly_add_reduced:
  ∀ p1 p2.
        reduce (p1 +p p2) = p1 +p p2
Proof
  gs[poly_add_def, reduce_idempotent]
QED

Theorem poly_mul_cst_reduced:
  ∀ c p.
    reduce (c *c p) = c *c p
Proof
  gs[poly_mul_cst_def, reduce_idempotent]
QED

Theorem poly_neg_reduced:
  ∀ p.
    reduce (--p p) = --p p
Proof
  gs[poly_neg_def, poly_mul_cst_reduced]
QED

Theorem poly_mul_reduced:
  ∀ p1 p2.
    reduce (p1 *p p2) = p1 *p p2
Proof
  Induct_on ‘p1’ >> gs[reduce_def, poly_mul_def, poly_add_reduced]
QED

Theorem poly_pow_reduced:
  ∀ p n.
    reduce (p **p n) = p **p n
Proof
  Induct_on ‘n’ >> gs[reduce_def, poly_pow_def, poly_mul_reduced]
QED

(* Relate to univariate HOL4 functions *)
Definition polyEvalsTo_def:
  polyEvalsTo (p:poly) x (r:real) ⇔
    evalPoly p x = r
End

Theorem polyEvalsTo_Var:
  ∀ x.
    polyEvalsTo (var n) x (x pow n)
Proof
  Induct_on ‘n’ >> gs[polyEvalsTo_def, evalPoly_def, var_def, pow]
QED

Theorem polyEvalsTo_Const:
  ∀ c x.
    polyEvalsTo (cst c) x c
Proof
  rpt strip_tac >> gs[polyEvalsTo_def, cst_def]
  >> cond_cases_tac >> gs[evalPoly_def]
QED

Theorem polyEvalsTo_MulCst:
  ∀ p1 r1 c x.
    polyEvalsTo p1 x r1 ⇒
    polyEvalsTo (c *c p1) x (c * r1)
Proof
  Induct_on ‘p1’
  >> gs[polyEvalsTo_def, evalPoly_def, poly_mul_cst_def, reduce_preserving,
        poly_mul_cst_aux_def]
  >> rpt strip_tac >> pop_assum kall_tac >> real_tac
QED

Theorem polyEvalsTo_Neg:
  ∀ p1 x r1.
    polyEvalsTo p1 x r1 ⇒
    polyEvalsTo (--p p1) x (- r1)
Proof
  rpt strip_tac >> pop_assum $ mp_then Any assume_tac polyEvalsTo_MulCst
  >> pop_assum $ qspec_then ‘-1’ assume_tac >> gs[poly_neg_def]
  >> real_tac
QED

Theorem polyEvalsTo_Add:
  ∀ p1 r1 p2 r2 x.
    polyEvalsTo p1 x r1 ⇒
    polyEvalsTo p2 x r2 ⇒
    polyEvalsTo (p1 +p p2) x (r1 + r2)
Proof
  Induct_on ‘p1’ >> rpt strip_tac
  >> gs[polyEvalsTo_def, evalPoly_def, poly_add_def, reduce_preserving,
        poly_add_aux_def]
  >> top_case_tac >> pop_assum $ rewrite_tac o single o GSYM
  >> gs[evalPoly_def]
  >> pop_assum $ rewrite_tac o single o GSYM
  >> pop_assum kall_tac
  >> real_tac
QED

Theorem polyEvalsTo_Sub:
  ∀ p1 r1 p2 r2 x.
    polyEvalsTo p1 x r1 ⇒
    polyEvalsTo p2 x r2 ⇒
    polyEvalsTo (p1 -p p2) x (r1 - r2)
Proof
  rpt strip_tac
  >> gs[poly_sub_def]
  >> pop_assum $ mp_then Any mp_tac polyEvalsTo_Neg
  >> pop_assum $ mp_then Any mp_tac polyEvalsTo_Add
  >> rpt strip_tac >> res_tac >> real_tac
QED

Theorem poly_add_aux_lid:
  poly_add_aux p [ ] = p ∧
  poly_add_aux p [0] = (if p = [] then [0] else p)
Proof
  Induct_on ‘p’
  >> rpt strip_tac
  >> gs[poly_add_aux_def]
QED

Theorem poly_add_lid:
  p +p [ ] = reduce p ∧
  p +p [0] = reduce p
Proof
  Induct_on ‘p’
  >> rpt strip_tac
  >> gs[poly_add_def, poly_add_aux_def, reduce_def, poly_add_aux_lid]
QED

Theorem polyEvalsTo_cons:
  x ≠ 0 ∧
  polyEvalsTo (c1::cs) x r ⇒
  polyEvalsTo cs x ((r - c1) / x)
Proof
  gs[polyEvalsTo_def, evalPoly_def] >> rpt strip_tac
  >> pop_assum $ gs o single o GSYM >> gs[real_div] >> real_tac
QED

Theorem polyEvalsTo_cons_zero:
  polyEvalsTo cs x r ⇒
  polyEvalsTo (0::cs) x (r * x)
Proof
  gs[polyEvalsTo_def, evalPoly_def]
QED

Theorem polyEvalsTo_Mul:
  ∀ p1 r1 p2 r2 x.
    polyEvalsTo p1 x r1 ⇒
    polyEvalsTo p2 x r2 ⇒
    polyEvalsTo (p1 *p p2) x (r1 * r2)
Proof
  Induct_on ‘p1’ >> rpt strip_tac
  >- gs[polyEvalsTo_def, evalPoly_def, poly_mul_def]
  >> ‘polyEvalsTo (h *c p2) x (h * r2)’
     by (irule polyEvalsTo_MulCst >> gs[])
  >> gs[poly_mul_def]
  >> first_assum $ mp_then Any mp_tac polyEvalsTo_Add
  >> cond_cases_tac
  >- gs[poly_add_lid, polyEvalsTo_def, evalPoly_def, poly_mul_cst_def, reduce_preserving]
  >> disch_then $ qspecl_then [‘0::(p1 *p p2)’] mp_tac
  >> Cases_on ‘x = 0’
  >- (
    gs[] >> disch_then $ qspec_then ‘0’ mp_tac
    >> impl_tac >> gs[polyEvalsTo_def, evalPoly_def])
  >> last_x_assum $ mp_then Any mp_tac polyEvalsTo_cons >> impl_tac >> gs[]
  >> disch_then (fn thm => last_x_assum (fn ithm => mp_then Any mp_tac ithm thm))
  >> disch_then (fn ithm => last_x_assum (fn thm => mp_then Any mp_tac ithm thm))
  >> strip_tac
  >> pop_assum $ mp_then Any assume_tac polyEvalsTo_cons_zero
  >> disch_then drule >> strip_tac
  >> gs[polyEvalsTo_def] >> real_tac
QED

Theorem polyEvalsTo_Pow:
  ∀ p n r x.
    polyEvalsTo p x r ⇒
    polyEvalsTo (p **p n) x (r pow n)
Proof
  Induct_on ‘n’
  >- gs[polyEvalsTo_def, evalPoly_def, poly_pow_def]
  >> rpt strip_tac >> res_tac
  >> last_x_assum $ mp_then Any mp_tac polyEvalsTo_Mul
  >> disch_then drule >> gs[poly_pow_def, pow]
QED

Theorem deep_embedding:
(∀ x. polyEvalsTo p x r) ⇒
∀ x. evalPoly p x = (λ x:real. r) x
Proof
  rpt strip_tac >> gs[polyEvalsTo_def]
QED

(** Connecting the semantics of HOL4 and realPoly **)
Theorem reduce_normalize_compat:
  reduce p = normalize p
Proof
  Induct_on ‘p’
  >- gs[reduce_def, normalize]
  >> rpt strip_tac >> gs[reduce_def, normalize]
QED

Theorem deg_degree:
  deg p = degree p
Proof
  gs[deg_def, degree, PRE_SUB1, reduce_normalize_compat]
QED

Theorem poly_compat:
  ∀p x. evalPoly p x = poly p x
Proof
  Induct_on ‘p’
  >- gs[evalPoly_def, poly_def]
  >> rpt strip_tac
  >> gs[evalPoly_def, poly_def]
QED

Definition compose_def:
  compose [] p = [] ∧
  compose (c::cs) p = [c] +p (p *p (compose cs p))
End

val _ = export_theory();
