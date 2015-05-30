open HolKernel Parse boolLib bossLib intLib;
open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open lcsymtacs closLangTheory sptreeTheory clos_annotateTheory;

val _ = new_theory "clos_call";


val _ = Datatype `
  val_approx = Clos num num (num list) (* name in code table, arity, extra args *)
             | Tuple (val_approx list)
             | Int int
             | Other
             | Impossible` (* value 'returned' by Raise *)

val getClos_def = Define `
  (getClos (Clos n a e) = SOME (n,a,e)) /\
  (getClos _ = NONE)`;

val any_el_def = Define `
  (any_el n [] d = d) /\
  (any_el n (x::xs) d = if n = 0 then x else any_el (n-1:num) xs d)`

val MEM_IMP_val_approx_size = prove(
  ``!vs a. MEM a vs ==> val_approx_size a < val_approx1_size vs``,
  Induct \\ fs [] \\ SRW_TAC [] [fetch "-" "val_approx_size_def"]
  \\ RES_TAC \\ DECIDE_TAC);

val adjust_vars_def = tDefine "adjust_vars" `
  (adjust_vars n (Tuple vs) = Tuple (MAP (adjust_vars n) vs)) /\
  (adjust_vars n (Clos name args extra_vars) =
     Clos name args (MAP (\k. k + n) extra_vars)) /\
  (adjust_vars n x = x)`
 (WF_REL_TAC `measure (val_approx_size o SND)` \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC MEM_IMP_val_approx_size \\ DECIDE_TAC)

val make_context_free_def = tDefine "adjust_vars" `
  (make_context_free (Tuple vs) = Tuple (MAP make_context_free vs)) /\
  (make_context_free (Clos name args []) = Clos name args []) /\
  (make_context_free (Clos name args xs) = Other) /\
  (make_context_free x = x)`
 (WF_REL_TAC `measure val_approx_size` \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC MEM_IMP_val_approx_size \\ DECIDE_TAC)

val merge_def = tDefine "merge" `
  (merge x y =
     case (x,y) of
     | (Impossible,y) => y
     | (x,Impossible) => x
     | (Tuple xs, Tuple ys) =>
          if LENGTH xs = LENGTH ys then
            Tuple (merge_list xs ys)
          else Other
     | (Clos _ _ _, Clos _ _ _) => if x = y then x else Other
     | (Int i, Int j) => if i = j then Int i else Other
     | _ => Other) /\
  (merge_list xs ys =
     case (xs,ys) of
     | (x::xs,y::ys) => merge x y :: merge_list xs ys
     | _ => [])`
 (WF_REL_TAC `measure
    (\x. case x of
         | INL (x,_) => val_approx_size x
         | INR (x,_) => val_approx1_size x)`)

val clos_exp1_size_lemma = prove(
  ``!fns n x. MEM (n,x) fns ==> clos_exp_size x < clos_exp1_size fns``,
  Induct \\ fs [FORALL_PROD,clos_exp_size_def] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ SRW_TAC [] [] \\ DECIDE_TAC);

val calls_op_def = Define `
  (calls_op (Global n) as g =
     case lookup n g of
     | NONE => (Other,g)
     | SOME x => (make_context_free x,g)) /\
  (calls_op (SetGlobal n) as g =
     case as of
     | (a::xs) => (Other,insert n a g)
     | _ => (Other,g)) /\
  (calls_op (Cons _) as g = (Tuple as,g)) /\
  (calls_op (Const i) as g = (Int i,g)) /\
  (calls_op El as g =
     case as of
     | [Tuple xs; Int i] =>
         if 0 <= i /\ i < &LENGTH xs
         then (EL (Num i) xs,g)
         else (Other,g)
     | _ => (Other,g)) /\
  (calls_op op as g = (Other,g))`

val calls_app_def = Define `
  calls_app loc arity e1 extras xs =
    if LENGTH xs < arity then
      App NONE e1 xs
    else if LENGTH xs = arity then
      Call loc (xs ++ MAP Var extras)
    else
      App NONE (Call loc (TAKE arity xs ++ MAP Var extras))
        (DROP arity xs)`

val adjust_all_def = Define `
  (adjust_all k [] = []) /\
  (adjust_all k (x::xs) = adjust_vars k x :: adjust_all (k+1) xs)`

val get_free_vars_def = Define `
  get_free_vars exps = vars_to_list (SND (cFree exps))`;

val list_max_def = Define `
  (list_max [] = 0:num) /\
  (list_max (x::xs) =
     let m = list_max xs in
       if m < x then x else m)`

(* This function avoids substitution in the body, instead it sets up a
   big Let that makes the new environemnt contain that equivalence
   original env as a prefix. *)
val calls_body_def = Define `
  calls_body num_args (fs:num list) body =
    let m = list_max fs in
      Let (GENLIST Var num_args ++
           GENLIST (\i. if MEM i fs then Var (i + num_args) else Op (Const 0) []) m)
        body`

val calls_def = tDefine "calls" `
  (calls [] vs (g:val_approx spt) = ([],[],g)) /\
  (calls ((x:clos_exp)::y::xs) vs g =
     let (e1,c1,g) = calls [x] vs g in
     let (e2,c2,g) = calls (y::xs) vs g in
       (e1 ++ e2,c1 ++ c2,g)) /\
  (calls [Var v] vs g =
     let a = adjust_vars v (any_el v vs Other) in
       ([(Var v,a)],[],g)) /\
  (calls [If x1 x2 x3] vs g =
     let (e1,c1,g) = calls [x1] vs g in
     let (e2,c2,g) = calls [x2] vs g in
     let (e3,c3,g) = calls [x3] vs g in
     let (e1,a1) = HD e1 in
     let (e2,a2) = HD e2 in
     let (e3,a3) = HD e3 in
       ([(If e1 e2 e3), merge a2 a3],c1++c2++c3,g)) /\
  (calls [Let xs x2] vs g =
     let (e1,c1,g) = calls xs vs g in
     let (e2,c2,g) = calls [x2] (adjust_all 0 (MAP SND e1) ++ vs) g in
     let (e2,a2) = HD e2 in
       ([(Let (MAP FST e1) e2, a2)],c1++c2,g)) /\
  (calls [Raise x1] vs g =
     let (e1,c1,g) = calls [x1] vs g in
     let (e1,a1) = HD e1 in
       ([(Raise e1,Impossible)],c1,g)) /\
  (calls [Tick x1] vs g =
     let (e1,c1,g) = calls [x1] vs g in
     let (e1,a1) = HD e1 in
       ([(Tick e1,a1)],c1,g)) /\
  (calls [Handle x1 x2] vs g =
     let (e1,c1,g) = calls [x1] vs g in
     let (e2,c2,g) = calls [x2] vs g in
     let (e1,a1) = HD e1 in
     let (e2,a2) = HD e2 in
       ([(Handle e1 e2,merge a1 a2)],c1++c2,g)) /\
  (calls [Call dest xs] vs g =
     let (e1,c1,l1) = calls xs vs g in
       ([(Call dest (MAP FST e1),Other)],c1,g)) /\
  (calls [Op op xs] vs g =
     let (e1,c1,g) = calls xs vs g in
     let (a,g) = calls_op op (MAP SND e1) g in
       ([(Op op (MAP FST e1),a)],c1,g)) /\
  (calls [App loc_opt x1 xs2] vs g =
     let (e1,c1,g) = calls [x1] vs g in
     let (e2,c2,g) = calls xs2 vs g in
     let (e1,a1) = HD e1 in
       case getClos a1 of
       | NONE => ([(App loc_opt e1 (MAP FST e2),Other)],c1++c2,g)
       | SOME (loc,arity,extras) =>
           ([(calls_app loc arity e1 extras (MAP FST e2),Other)],c1++c2,g)) /\
  (calls [Fn loc ws num_args x1] vs g =
     let (e1,c1,g) = calls [x1] (REPLICATE num_args Other ++ vs) g in
     let (body,a1) = HD e1 in
     let fs = get_free_vars [Fn loc ws num_args body] in
     let call = Call loc (GENLIST Var num_args ++ MAP Var fs) in
       ([(Fn loc [] num_args call,Clos loc num_args [])],
        (loc,num_args + LENGTH fs, calls_body num_args fs body)::c1,g)) /\
  (calls [Letrec loc _ fns x1] vs g = ARB)`
 (WF_REL_TAC `measure (clos_exp3_size o FST)`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC clos_exp1_size_lemma \\ DECIDE_TAC);

(* The first run of calls is just there to figure out what is assigned
   to the globals. *)
val cCallIntro_def = Define `
  cCallIntro exps =
    let (es,code,g) = calls exps [] LN in
    let (es,code,g) = calls exps [] g in
      (MAP FST es,code)`



(*

TODO:
 - implement Letrec
 - write examples to see if it works as expected
 - separate locs at the end of cCallIntro

Intended use:
  intro_multi --> cCallIntro --> cDeadElim --> cAnnotate --> cDeadElim --> cComp

*)

val _ = export_theory();
