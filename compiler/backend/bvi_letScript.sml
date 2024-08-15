(*

   This is a BVI transformation that propagates variable lookups that
   are immediately assigned to a new variable in Let bindings. This
   optimisation is to run immediately when entering BVI.

   This optimisation removes each Var in a Let, i.e.

     Let [ ... ; Var ... ; ... ] ...

   and replaces them with constants

     Let [ ... ; Op (Const _) [] ; ... ] ....

   and then replaces all occurrences of the bound var in the body with
   a lookup to the original variable.

   There is a similar optimisation in BVL (bvl_const). This version
   (which is slightly simpler) is run again because the BVL-to-BVI
   compiler can introduce large Let expressions consisting of only
   variable lookups.

   This BVI version differs from the BVL version (bvl_const) by having
   the ability to move expressions into tail-position, e.g.

     let
       val x = foo ...
       val y = bar x
     in y end

   becomes:

     let
       val x = foo ...
     in bar x end

   This is important because pat-to-clos translates Seq p1 p2 into
   Let [compile p1; compile p2] (Var 1).

*)
open preamble bviTheory;

val _ = new_theory "bvi_let";

Definition extract_def:
  (extract ((Var n):bvi$exp) ys = n + LENGTH ys + 1) /\
  (extract _ _ = 0)
End

Definition extract_list_def:
  (extract_list [] = []) /\
  (extract_list (x::xs) = extract x xs :: extract_list xs)
End

Definition delete_var_def:
  (delete_var ((Var n):bvi$exp) = Op (Const 0) []) /\
  (delete_var x = x)
End

Theorem exp2_size_APPEND:
   !xs ys. exp2_size (xs++ys) = exp2_size xs + exp2_size ys
Proof
  Induct \\ fs [exp_size_def]
QED

Definition compile_def:
  (compile env d [] = []) /\
  (compile env d (x::y::xs) = compile env d [x] ++ compile env d (y::xs)) /\
  (compile env d [(Var v):bvi$exp] =
     case LLOOKUP env v of
     | SOME n => [Var (v + n)]
     | _ => [Var (v + d)]) /\
  (compile env d [If x1 x2 x3] =
     [If (HD (compile env d [x1]))
         (HD (compile env d [x2]))
         (HD (compile env d [x3]))]) /\
  (compile env d [Let xs x2] =
     let l = LENGTH xs in
       if l = 0 then compile env d [x2] else
         let k = l-1 in
           if x2 = Var k then
             (* moves the last exp into tail-position if the body is a Var *)
             let ys = compile env d (BUTLAST xs) in
               [Let ys (HD (compile (MAP ((+)k) env) (d+k) [LAST xs]))]
           else
             let ys = compile env d xs in
               [Let (MAP delete_var ys)
                 (HD (compile (extract_list ys ++ env) d [x2]))]) /\
  (compile env d [Raise x1] =
     [Raise (HD (compile env d [x1]))]) /\
  (compile env d [Op op xs] = [Op op (compile env d xs)]) /\
  (compile env d [Tick x] = [Tick (HD (compile env d [x]))]) /\
  (compile env d [Call t dest xs h] =
     [Call t dest (compile env d xs)
         (case h of NONE => NONE
                  | SOME e => SOME (HD (compile (0::env) d [e])))])
Termination
  WF_REL_TAC `measure (bvi$exp2_size o SND o SND)`
  \\ rw [] \\ fs [LENGTH_NIL]
  \\ imp_res_tac (METIS_PROVE [SNOC_CASES] ``m <> [] ==> ?x y. m = SNOC x y``)
  \\ full_simp_tac std_ss [LAST_SNOC,LENGTH_SNOC,FRONT_SNOC]
  \\ fs [exp2_size_APPEND,SNOC_APPEND,exp_size_def]
End

Definition compile_sing_def:
  (compile_sing env d ((Var v):bvi$exp) =
     case LLOOKUP env v of
     | SOME n => Var (v + n)
     | _ => Var (v + d)) /\
  (compile_sing env d (If x1 x2 x3) =
     (If (compile_sing env d x1)
         (compile_sing env d x2)
         (compile_sing env d x3))) /\
  (compile_sing env d (Let xs x2) =
     let l = LENGTH xs in
       if l = 0 then compile_sing env d x2 else
         let k = l-1 in
           if x2 = Var k then
             (* moves the last exp into tail-position if the body is a Var *)
             let ys = compile_list env d (BUTLAST xs) in
               (Let ys ((compile_sing (MAP ((+)k) env) (d+k) (LAST xs))))
           else
             let ys = compile_list env d xs in
               (Let (MAP delete_var ys)
                 ((compile_sing (extract_list ys ++ env) d x2)))) /\
  (compile_sing env d (Raise x1) =
     (Raise ((compile_sing env d x1)))) /\
  (compile_sing env d (Op op xs) = (Op op (compile_list env d xs))) /\
  (compile_sing env d (Tick x) = (Tick (compile_sing env d x))) /\
  (compile_sing env d (Call t dest xs h) =
     (Call t dest (compile_list env d xs)
         (case h of NONE => NONE
                  | SOME e => SOME ((compile_sing (0::env) d e))))) /\
  (compile_list env d [] = []) /\
  (compile_list env d (x::xs) =
    compile_sing env d x :: compile_list env d xs)
Termination
  WF_REL_TAC ‘measure $ λx. case x of
                            | INL (_,_,e) => bvi$exp_size e
                            | INR (_,_,es) => bvi$exp2_size es’
  \\ conj_tac \\ Cases using SNOC_CASES
  \\ gvs [SNOC_APPEND,exp2_size_APPEND,bviTheory.exp_size_def]
End

Theorem compile_sing:
  (∀n d e. compile n d [e] = [compile_sing n d e]) ∧
  (∀n d e. compile_list n d e = compile n d e)
Proof
  ho_match_mp_tac compile_sing_ind \\ rpt strip_tac
  \\ gvs [compile_sing_def,compile_def]
  \\ every_case_tac \\ gvs []
  \\ rename [‘compile n d (e::es)’]
  \\ Cases_on ‘es’ \\ gvs []
  \\ gvs [compile_sing_def,compile_def]
QED

Theorem compile_length[simp]:
   !n d xs. LENGTH (compile n d xs) = LENGTH xs
Proof
  HO_MATCH_MP_TAC compile_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [compile_def,ADD1,LET_DEF]
  \\ every_case_tac \\ SRW_TAC [] [] \\ DECIDE_TAC
QED

Theorem compile_HD_SING:
   [HD (compile n d [x])] = compile n d [x]
Proof
  MP_TAC (Q.SPECL [`n`,`d`,`[x]`] compile_length)
  \\ Cases_on `compile n d [x]` \\ fs [LENGTH_NIL]
QED

Definition compile_exp_def:
  compile_exp x =
    case compile [] 0 [x] of (y::_) => y | _ => Var 0 (* impossible *)
End

Theorem compile_exp_eq = compile_exp_def |> SRULE [compile_sing];

val _ = export_theory();
