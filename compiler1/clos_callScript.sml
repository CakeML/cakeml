open preamble closLangTheory clos_freeTheory;

val _ = new_theory "clos_call";

val get_free_vars_def = Define `
  get_free_vars exps = vars_to_list (SND (free exps))`;

val _ = Datatype `
  val_approx = Clos num num (num list) (* name in code table, arity, extra args *)
             | Tuple (val_approx list)
             | Int int
             | Other
             | Impossible` (* value 'returned' by Raise *)

val dest_Clos_def = Define `
  (dest_Clos (Clos n a e) = SOME (n,a,e)) /\
  (dest_Clos _ = NONE)`;
val _ = export_rewrites["dest_Clos_def"];

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

val calls_op_def = Define `
  (calls_op (Global n) as g =
     case lookup n g of
     | NONE => (Other,g)
     | SOME x => (make_context_free x,g)) /\
  (calls_op (SetGlobal n) as g =
     case as of
     | [] => (Other,g)
     | (a::xs) =>
       case lookup n g of
       | NONE => (Other,insert n a g)
       | SOME other => (Other,insert n Other g)) /\
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

val pure_op_def = Define `
  (pure_op Add = T) /\
  (pure_op Sub = T) /\
  (pure_op Mult = T) /\
  (pure_op Div = T) /\
  (pure_op Mod = T) /\
  (pure_op (Const _) = T) /\
  (pure_op El = T) /\
  (pure_op (Global _) = T) /\
  (pure_op _ = F)` (* not complete *)

val exp3_size_lemma = prove(
  ``!xs a. MEM a xs ==> exp_size a < exp3_size xs``,
  Induct \\ fs []
  \\ SRW_TAC [] [exp_size_def] \\ RES_TAC \\ DECIDE_TAC);

val pure_def = tDefine "pure" `
  (pure (Var v) = T) /\
  (pure (Op op xs) <=> pure_op op /\ EVERY pure xs) /\
  (pure (Fn _ _ _ _) <=> T) /\
  (pure (Letrec _ _ _ x) <=> pure x) /\
  (pure (If x1 x2 x3) <=> pure x1 /\ pure x2 /\ pure x3) /\
  (pure (Let xs x) <=> EVERY pure xs /\ pure x) /\
  (pure _ = F)`
 (WF_REL_TAC `measure (exp_size)`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC exp3_size_lemma \\ DECIDE_TAC);

val Seq_def = Define `
  Seq e1 e2 =
    if pure e1 then e2 else Let [e1;e2] (Var 1)`;

val calls_app_def = Define `
  calls_app loc arity e1 extras xs =
    if LENGTH xs < arity then
      App NONE e1 xs
    else if LENGTH xs = arity then
      Seq e1 (Call loc (xs ++ MAP (\i. Var (i + arity)) extras))
    else
      Seq e1 (App NONE (Call loc (TAKE arity xs ++ MAP Var extras))
        (DROP arity xs))`

val adjust_all_def = Define `
  (adjust_all k [] = []) /\
  (adjust_all k (x::xs) = adjust_vars k x :: adjust_all (k+1) xs)`

(* This function avoids substitution in the body, instead it sets up a
   big Let that makes the new environemnt contain that equivalence
   original env as a prefix. *)
val calls_body_def = Define `
  calls_body num_args (fs1:num list) body =
    let m = list_max (MAP (\i. i + 1) fs1) in
      Let (GENLIST Var num_args ++
           GENLIST (\i. if MEM i fs1
                        then Var (num_args + index_of i fs1)
                        else Op (Const 0) []) m)
        body`

val EL_MEM_LEMMA = prove(
  ``!xs i x. i < LENGTH xs /\ (x = EL i xs) ==> MEM x xs``,
  Induct \\ fs [] \\ REPEAT STRIP_TAC \\ Cases_on `i` \\ fs []);

val calls_def = tDefine "calls" `
  (calls [] vs (g:val_approx spt) = ([],[],g)) /\
  (calls ((x:closLang$exp)::y::xs) vs g =
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
       case dest_Clos a1 of
       | NONE => ([(App loc_opt e1 (MAP FST e2),Other)],c1++c2,g)
       | SOME (loc,arity,extras) =>
           ([(calls_app loc arity e1 extras (MAP FST e2),Other)],c1++c2,g)) /\
  (calls [Fn loc ws num_args x1] vs g =
     let (e1,c1,g1) = calls [x1] (REPLICATE num_args Other ++ vs) g in
     let (body,a1) = HD e1 in
     let fs1 = get_free_vars [Fn loc ws num_args body] in
     let fs = MAP (\i. i + num_args) fs1 in
     let call = Call loc (GENLIST Var num_args ++ MAP Var fs) in
       ([(Fn loc [] num_args call,Clos loc num_args fs)],
        (loc,num_args + LENGTH fs, calls_body num_args fs1 body)::c1,g)) /\
  (calls [Letrec loc _ fns x1] vs g =
     (* compute free variables (fs1), note: closure itself might be free
        after call-intro if its isn't fully applied at rec calls *)
     let fake_vs = GENLIST (\i. Clos (loc + i) (FST (EL i fns)) []) (LENGTH fns) in
     let res = MAP (\(num_args,x).
                       let new_vs = REPLICATE num_args Other ++ fake_vs ++ vs in
                       let res = calls [x] new_vs g in
                         (Fn 0 [] num_args (FST (HD (FST res))))) fns in
     let fs1 = get_free_vars res in
       (* If some of the mutually recursive closures were not fully
          applied within the body, then don't perform call-intro.
          Reason: the proofs are complicated and the
          call-intro-generated code is only sometimes better than the
          original. Example:
            fun tree_map f (Tree x xs) = Tree (f x) (map (tree_map f) xs)
          where call-intro makes the code slightly worse. *)
       if LENGTH (list_inter (GENLIST I (LENGTH fns)) fs1) <> 0 then
         let new_vs = MAP (K Other) fns in (* <--- could be more precise *)
         let (e1,xs,g) = calls [x1] (new_vs++vs) g in
         let (e1,a1) = HD e1 in
           ([(Letrec loc [] fns e1,a1)],xs,g)
       else
         let fns1 = GENLIST
             (\i. if LENGTH fns <= i then (Var 0) else
                    let (num_args,x) = EL i fns in
                    let fs = MAP (\i. i + num_args) fs1 in
                    let call = Call (loc+i) (GENLIST Var num_args ++ MAP Var fs) in
                      (Fn (loc+i:num) [] num_args call)) (LENGTH fns) in
         let new_vs = GENLIST (\i. Clos (loc + i) (FST (EL i fns)) fs1)
                        (LENGTH fns) in
         let new_code = GENLIST
             (\i. if LENGTH fns <= i then (0,0,Var 0) else
                    let (num_args,x) = EL i fns in
                    let fs = MAP (\i. i + num_args) fs1 in
                    let new_vs = REPLICATE num_args Other ++ new_vs ++ vs in
                    let res = calls [x] new_vs g in
                    let body = FST (HD (FST res)) in
                      (loc + i, num_args + LENGTH fs1,
                       calls_body num_args fs1 body)) (LENGTH fns) in
         let (e1,xs,g) = calls [x1] (new_vs++vs) g in
         let (e1,a1) = HD e1 in
           ([(Let fns1 e1,a1)],new_code++xs,g))`
 (WF_REL_TAC `measure (exp3_size o FST)`
  \\ REPEAT STRIP_TAC
  \\ fs [GSYM NOT_LESS]
  \\ IMP_RES_TAC EL_MEM_LEMMA
  \\ IMP_RES_TAC exp1_size_lemma
  \\ DECIDE_TAC);

(* The first run of calls is just there to figure out what is assigned
   to the globals. *)
val call_intro_def = Define `
  call_intro exps =
    let (es,code,g) = calls exps [] LN in
    let (es,code,g) = calls exps [] g in
      (MAP FST es,code)`

(* --- tests --- *)

(*
  val g = fn [y; z] => let
            val f = fn x => x + (y - z)
            in f 5 end
*)

  val f = ``Fn 500 [] 1 (Op Add [Var 0; Op Sub [Var 1; Var 2]])``
  val g = ``Fn 400 [] 2 (Let [^f] (App NONE (Var 0) [Op (Const 5) []]))``
  val ev = EVAL ``call_intro [^f]``
  val ev = EVAL ``call_intro [^g]``

(*
  val g = fn [y; z] => (fn x => x + (y - z)) 5
*)

  val f = ``Fn 500 [] 1 (Op Add [Var 0; Op Sub [Var 1; Var 2]])``
  val g = ``Fn 400 [] 2 ((App NONE (^f) [Op (Const 5) []]))``
  val ev = EVAL ``call_intro [^f]``

(*
  let val xy =
        let val f = fn k => k + 1
            val g = fn k => k - 1
            in (f,g) end
  in #1 xy 4 end
  -->
  let val xy = ...
  in call_f 4 end
*)

  val f = ``Fn 800 [] 1 (Op Add [Var 0; Op (Const 1) []])``
  val g = ``Fn 900 [] 1 (Op Sub [Var 0; Op (Const 1) []])``
  val xy = ``Let [^f;^g] (Op (Cons 0) [Var 0; Var 1])``
  val app = ``Let [^xy] (App NONE (Op El [Var 0; Op (Const 0) []]) [Op (Const 4) []])``
  val ev = EVAL ``call_intro [^app]``

(*
  let
    val f = fn k => (get_global 60) (k + 1)
    val g = set_global 60 f
  in f 4 end
  -->
  call-table implementation of f does not use globals
  `f 4` is optimised to a simple call
*)

  val f = ``Fn 900 [] 1 (App NONE (Op (Global 60) []) [Op Add [Var 0; Op (Const 1) []]])``
  val g = ``Op (SetGlobal 60) [Var 0]``
  val exp = ``Let [^f] (Let [^g] (App NONE (Var 1) [Op (Const 4) []]))``
  val ev = EVAL ``call_intro [^exp]``

(*
  let fun f x = f x in f end
*)

  val f = ``Letrec 200 [] [(1,App NONE (Var 1) [Var 0])] (Var 0)``
  val ev = EVAL ``call_intro [^f]``

(*
  fn [t;q] => let fun f x y = f (x - t) (y - q) in f end
*)

  val f = ``Letrec 200 [] [(2,App NONE (Var 2)
              [Op Sub [Var 0; Var 3]; Op Sub [Var 1; Var 4]])]
                (Var 0)``
  val exp = ``Fn 100 [] 2 ^f``
  val ev = EVAL ``call_intro [^exp]``


(*

TODO:
 - separate locs at the end of call_intro
 - implement dead_elim (and var_simp)

Intended use:
  intro_multi --> call_intro --> dead_elim --> annotate --> dead_elim --> compile

*)

val _ = export_theory();
