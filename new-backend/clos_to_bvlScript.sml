open HolKernel Parse boolLib bossLib; val _ = new_theory "clos_to_bvl";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open lcsymtacs closLangTheory bvlTheory;

(* compiler definition *)

val free_let_def = Define `
  free_let n = (GENLIST (\n. Op (El (n+1)) [Var 1]) n) : bvl_exp list`;

val closure_tag_def = Define `
  closure_tag = 0:num`;

val cComp_def = tDefine "cComp" `
  (cComp n [] aux = ([],aux,n)) /\
  (cComp n ((x:clos_exp)::y::xs) aux =
     let (c1,aux1,n1) = cComp n [x] aux in
     let (c2,aux2,n2) = cComp n1 (y::xs) aux1 in
       (c1 ++ c2, aux2, n2)) /\
  (cComp n [Var v] aux = ([(Var v):bvl_exp], aux, n)) /\
  (cComp n [If x1 x2 x3] aux =
     let (c1,aux1,n1) = cComp n [x1] aux in
     let (c2,aux2,n2) = cComp n1 [x2] aux1 in
     let (c3,aux3,n3) = cComp n2 [x3] aux2 in
       ([If (HD c1) (HD c2) (HD c3)],aux3,n3)) /\
  (cComp n [Let xs x2] aux =
     let (c1,aux1,n1) = cComp n xs aux in
     let (c2,aux2,n2) = cComp n1 [x2] aux1 in
       ([Let c1 (HD c2)], aux2, n2)) /\
  (cComp n [Raise x1] aux =
     let (c1,aux1,n1) = cComp n [x1] aux in
       ([Raise (HD c1)], aux1, n1)) /\
  (cComp n [Tick x1] aux =
     let (c1,aux1,n1) = cComp n [x1] aux in
       ([Tick (HD c1)], aux1, n1)) /\
  (cComp n [Op op xs] aux =
     let (c1,aux1,n1) = cComp n xs aux in
       ([Op op c1],aux1,n1)) /\
  (cComp n [App x1 x2] aux =
     let (c1,aux1,n1) = cComp n [x1] aux in
     let (c2,aux2,n2) = cComp n1 [x2] aux1 in
       ([Let (c1++c2)
           (Call NONE ((Var 1) ::          (* argument *)
                       (Var 0) ::          (* closure itself *)
                       [Op (El 0) [Var 0]] (* code pointer *)))],
        aux2, n2)) /\
  (cComp n [Fn vs x1] aux =
     let (c1,aux1,n1) = cComp n [x1] aux in
     let c2 = Let ((Var 0:bvl_exp) :: free_let (LENGTH vs)) (HD c1) in
       ([Op (Cons closure_tag) (Op (Label n1) [] :: MAP Var vs)],
        (n1,c2) :: aux1, n1+1)) /\
  (cComp n [Handle x1 x2] aux =
     let (c1,aux1,n1) = cComp n [x1] aux in
     let (c2,aux2,n2) = cComp n1 [x2] aux1 in
       ([Handle (HD c1) (HD c2)], aux2, n2)) /\
  (cComp n [Call dest xs] aux =
     let (c1,aux1,n1) = cComp n xs aux in
       ([Call (SOME dest) c1],aux1,n1))`
 (WF_REL_TAC `measure (clos_exp1_size o FST o SND)`
  \\ REPEAT STRIP_TAC \\ DECIDE_TAC);

(* correctness proof *)

val (val_rel_rules,val_rel_ind,val_rel_cases) = Hol_reln `
  (val_rel code (Number i) (Number i)) /\
  (EVERY2 (val_rel code) xs (ys:bc_value list) ==>
   val_rel code (Block t xs) (Block t ys)) /\
  (val_rel code (RefPtr p1) (RefPtr p1)) /\ (* <-- needs changing *)
  (EVERY2 (val_rel code) xs ys /\
   (cComp n [x] aux = ([c],aux1,n1)) /\
   (lookup p code = SOME (2:num,c)) ==>
   val_rel code (Closure env x) (Block closure_tag (CodePtr p :: ys)))`

val opt_val_rel_def = Define `
  (opt_val_rel code NONE NONE = T) /\
  (opt_val_rel code (SOME x) (SOME y) = val_rel code x y) /\
  (opt_val_rel code _ _ = F)`;

val (res_rel_rules,res_rel_ind,res_rel_cases) = Hol_reln `
  (EVERY2 (val_rel code) xs (ys:bc_value list) ==>
   res_rel code (Result xs) (Result ys)) /\
  (val_rel code x y ==>
   res_rel code (Exception x) (Exception y)) /\
  (res_rel code TimeOut TimeOut) /\
  (res_rel code Error Error)`

val env_rel_def = Define `
  (env_rel code [] [] = T) /\
  (env_rel code [] ys = T) /\   (* bvl env allowed to contain extra stuff *)
  (env_rel code (x::xs) [] = F) /\
  (env_rel code (x::xs) (y::ys) <=> val_rel code x y /\ env_rel code xs ys)`;

val code_installed_def = Define `
  code_installed aux (t:bvl_state) =
    EVERY (\(n,exp). lookup n t.code = SOME (2:num,exp)) aux`;

val state_rel_def = Define `
  state_rel (s:clos_state) (t:bvl_state) <=>
    (s.clock = t.clock) /\
    (s.output = t.output) /\
    (EVERY2 (opt_val_rel t.code) s.globals t.globals /\
    (* TODO: refs need relating too *)
    (!name arity c.
      (FLOOKUP s.code name = SOME (arity,c)) ==>
      ?n1 aux1 n2 c2 aux2.
        (cComp n1 [c] aux1 = ([c2],aux2,n2)) /\
        (lookup name t.code = SOME (arity,c2)) /\
        code_installed aux2 t))`

val cComp_correct = prove(
  ``!xs env s1 n res s2 t1 n2 ys aux1 aux2 env'.
      (cEval (xs,env,s1) = (res,s2)) /\ res <> Error /\
      (cComp n xs aux1 = (ys,aux2,n2)) /\
      code_installed aux2 t1 /\
      env_rel t1.code env env' /\
      state_rel s1 t1 ==>
      ?res' t2.
         (bEval (ys,env',t1) = (res',t2)) /\
         res_rel t1.code res res' /\
         state_rel s2 t2``,
  recInduct cEval_ind \\ REPEAT STRIP_TAC
  THEN1 (* NIL *) cheat
  THEN1 (* CONS *) cheat
  THEN1 (* Var *) cheat
  THEN1 (* If *) cheat
  THEN1 (* Let *) cheat
  THEN1 (* Raise *) cheat
  THEN1 (* Handle *) cheat
  THEN1 (* Op *) cheat
  THEN1 (* Fn *) cheat
  THEN1 (* App *) cheat
  THEN1 (* Tick *) cheat
  THEN1 (* Call *) cheat);

val _ = export_theory();
