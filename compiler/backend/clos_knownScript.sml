open preamble closLangTheory;

val _ = new_theory "clos_known";

(* -----------------------------------------------------------------

  This compiler transformation turns App NONEs into APP SOMEs.
  An App can carry a `SOME loc` if:
   1) the closure value that is used there was created with location loc;
   2) the closure value exepcts the number of arguments it gets here.

  This part of the compiler makes two passes. The first pass tracks
  which closure values flow into which globals. The second pass tracks
  closure values (with help of the result of the first pass) and
  switches App NONEs into App SOMEs wherever possible.

   ----------------------------------------------------------------- *)

val _ = Datatype `
  val_approx = Clos num num (* location in code table, arity *)
             | Tuple (val_approx list) (* conses or tuples *)
             | Int int      (* used to index tuples *)
             | Other        (* unknown *)
             | Impossible`  (* value 'returned' by Raise *)

val merge_def = tDefine "merge" `
  (merge x y =
     case (x,y) of
     | (Impossible,y) => y
     | (x,Impossible) => x
     | (Tuple xs, Tuple ys) =>
          if LENGTH xs = LENGTH ys then
            Tuple (merge_list xs ys)
          else Other
     | (Clos _ _, Clos _ _) => if x = y then x else Other
     | (Int i, Int j) => if i = j then x else Other
     | _ => Other) /\
  (merge_list xs ys =
     case (xs,ys) of
     | (x::xs,y::ys) => merge x y :: merge_list xs ys
     | _ => [])`
 (WF_REL_TAC `measure
    (\x. case x of
         | INL (x,_) => val_approx_size x
         | INR (x,_) => val_approx1_size x)`)

val known_op_def = Define `
  (known_op (Global n) as g =
     case lookup n g of
     | NONE => (Other,g)
     | SOME x => (x,g)) /\
  (known_op (SetGlobal n) as g =
     case as of
     | [] => (Other,g)
     | (a::xs) =>
       case lookup n g of
       | NONE => (Other,insert n a g)
       | SOME other => (Other,insert n (merge other a) g)) /\
  (known_op (Cons _) as g = (Tuple as,g)) /\
  (known_op (Const i) as g = (Int i,g)) /\
  (known_op El as g =
     case as of
     | [Tuple xs; Int i] =>
         if 0 <= i /\ i < &LENGTH xs
         then (EL (Num i) xs,g)
         else (Other,g)
     | _ => (Other,g)) /\
  (known_op op as g = (Other,g))`

val EL_MEM_LEMMA = prove(
  ``!xs i x. i < LENGTH xs /\ (x = EL i xs) ==> MEM x xs``,
  Induct \\ fs [] \\ REPEAT STRIP_TAC \\ Cases_on `i` \\ fs []);

val dest_Clos_def = Define `
  (dest_Clos (Clos n a) = SOME (n,a)) /\
  (dest_Clos _ = NONE)`;
val _ = export_rewrites["dest_Clos_def"];

val known_def = tDefine "known" `
  (known [] vs (g:val_approx spt) = ([],g)) /\
  (known ((x:closLang$exp)::y::xs) vs g =
     let (e1,g) = known [x] vs g in
     let (e2,g) = known (y::xs) vs g in
       (e1 ++ e2,g)) /\
  (known [Var v] vs g =
     ([(Var v,any_el v vs Other)],g)) /\
  (known [If x1 x2 x3] vs g =
     let (e1,g) = known [x1] vs g in
     let (e2,g) = known [x2] vs g in
     let (e3,g) = known [x3] vs g in
     let (e1,a1) = HD e1 in
     let (e2,a2) = HD e2 in
     let (e3,a3) = HD e3 in
       ([(If e1 e2 e3), merge a2 a3],g)) /\
  (known [Let xs x2] vs g =
     let (e1,g) = known xs vs g in
     let (e2,g) = known [x2] (MAP SND e1 ++ vs) g in
     let (e2,a2) = HD e2 in
       ([(Let (MAP FST e1) e2, a2)],g)) /\
  (known [Raise x1] vs g =
     let (e1,g) = known [x1] vs g in
     let (e1,a1) = HD e1 in
       ([(Raise e1,Impossible)],g)) /\
  (known [Tick x1] vs g =
     let (e1,g) = known [x1] vs g in
     let (e1,a1) = HD e1 in
       ([(Tick e1,a1)],g)) /\
  (known [Handle x1 x2] vs g =
     let (e1,g) = known [x1] vs g in
     let (e2,g) = known [x2] vs g in
     let (e1,a1) = HD e1 in
     let (e2,a2) = HD e2 in
       ([(Handle e1 e2,merge a1 a2)],g)) /\
  (known [Call dest xs] vs g =
     let (e1,l1) = known xs vs g in
       ([(Call dest (MAP FST e1),Other)],g)) /\
  (known [Op op xs] vs g =
     let (e1,g) = known xs vs g in
     let (a,g) = known_op op (MAP SND e1) g in
       ([(Op op (MAP FST e1),a)],g)) /\
  (known [App loc_opt x xs] vs g =
     let (e1,g) = known [x] vs g in
     let (e2,g) = known xs vs g in
     let (e1,a1) = HD e1 in
     let new_loc_opt = (case dest_Clos a1 of
                        | NONE => NONE
                        | SOME (loc,arity) => if arity = LENGTH xs
                                              then SOME loc else NONE) in
       ([(App new_loc_opt e1 (MAP FST e2),Other)],g)) /\
  (known [Fn loc_opt ws num_args x1] vs g =
     let (e1,g) = known [x1] (REPLICATE num_args Other ++ vs) g in
     let (body,a1) = HD e1 in
       ([(Fn loc_opt ws num_args body,
          case loc_opt of
          | SOME loc => Clos loc num_args
          | NONE => Other)],g)) /\
  (known [Letrec loc_opt _ fns x1] vs g =
     let loc = (case loc_opt of NONE => 0 | SOME n => n) in
     let clos = GENLIST (\i. Clos (loc + i) (FST (EL i fns))) (LENGTH fns) in
     (* The following ignores SetGlobal within fns, but it shouldn't
        appear there, and missing it just means this opt will do less. *)
     let new_fns = MAP (\(num_args,x).
                    let new_vs = REPLICATE num_args Other ++ clos ++ vs in
                    let res = known [x] new_vs g in
                      (num_args,FST (HD (FST res)))) fns in
     let (e1,g) = known [x1] (clos ++ vs) g in
     let (e1,a1) = HD e1 in
       ([(Letrec loc_opt NONE new_fns e1,a1)],g))`
 (WF_REL_TAC `measure (exp3_size o FST)`
  \\ REPEAT STRIP_TAC
  \\ fs [GSYM NOT_LESS]
  \\ IMP_RES_TAC EL_MEM_LEMMA
  \\ IMP_RES_TAC exp1_size_lemma
  \\ DECIDE_TAC);

val compile_def = Define `
  compile F exp = exp /\
  compile T exp =
    let (_,g) = known [exp] [] LN in
    let (e,_) = known [exp] [] g in
      FST (HD e)`

(*

  TEST 1

  let fun f x = f x in f end

  val f = ``Letrec (SOME 200) NONE [(1,App NONE (Var 1) [Var 0])] (Var 0)``
  val ev = EVAL ``compile T ^f``

  TEST 2

  let
    val f = fn k => (get_global 60) (k + 1)
    val g = set_global 60 f
  in f 4 end

  val f = ``Fn (SOME 900) NONE 1 (App NONE (Op (Global 60) []) [Op Add [Var 0; Op (Const 1) []]])``
  val g = ``closLang$Op (SetGlobal 60) [Var 0]``
  val exp = ``Let [^f] (Let [^g] (App NONE (Var 1) [Op (Const 4) []]))``
  val ev = EVAL ``compile T ^exp``

  TEST 2A

  let
    val f = fn k => k + 1
    val g = set_global 60 f
  in
    get_global 60 3
  end

  val f = ``Fn (SOME 900) NONE 1 (Op Add [Var 0; Op (Const 1) []])``
  val g = ``closLang$Op (SetGlobal 60) [Var 0]``
  val exp = ``Let [^f] (Let [^g] (App NONE
                                      (Op (Global 60) [])
                                      [Op (Const 3) []]))``
  val ev = EVAL ``compile T ^exp``



  TEST 3

  let val xy =
        let val f = fn k => k + 1
            val g = fn k => k - 1
            in (f,g) end
  in #1 xy 4 end


  val f = ``Fn (SOME 800) NONE 1 (Op Add [Var 0; Op (Const 1) []])``
  val g = ``Fn (SOME 900) NONE 1 (Op Sub [Var 0; Op (Const 1) []])``
  val xy = ``Let [^f;^g] (Op (Cons 0) [Var 0; Var 1])``
  val app = ``Let [^xy] (App NONE (Op El [Var 0; Op (Const 0) []]) [Op (Const 4) []])``
  val ev = EVAL ``compile T ^app``

*)

val _ = export_theory();
