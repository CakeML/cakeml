(*
  Constructed product result (CPR) optimisation for BVI.

  A function whose tail positions all build [Cons] blocks of one shape
  (or raise, or tail call functions already split with that shape) is
  split in two. The worker, at a fresh name, returns the fields with
  [Return], in [Op] argument order. The wrapper keeps the original name
  and is [LetCall w 0 worker (GENLIST Var arity) (rebuild 0 sh)]: it calls
  the worker and rebuilds the block. Tail calls to split functions in a
  worker become tail calls to their workers.
*)
Theory bvi_cpr
Ancestors
  bvi backend_common[qualified] bvi_inline[qualified]
Libs
  preamble

Datatype:
  cpr_shape = Leaf
            | ConsShape num (cpr_shape list)
            | Flexible
End

Definition sub_shape_def:
  (sub_shape Leaf _ = T) ∧
  (sub_shape (ConsShape n1 l1) (ConsShape n2 l2) = if n1 = n2 then sub_shape_list l1 l2 else F) ∧
  (sub_shape _ Flexible = T) ∧
  (sub_shape _ _ = F) ∧

  (sub_shape_list [] [] = T) ∧
  (sub_shape_list (e::es) (e'::es') = (sub_shape e e' ∧ sub_shape_list es es')) ∧
  (sub_shape_list _ _ = F)
End

Definition cpr_merge_def:
  (cpr_merge _ Leaf = Leaf) ∧
  (cpr_merge Leaf _ = Leaf) ∧
  (cpr_merge sh Flexible = sh) ∧
  (cpr_merge Flexible sh = sh) ∧
  (cpr_merge (ConsShape t1 xs) (ConsShape t2 ys) =
   if t1 = t2 /\ LENGTH xs = LENGTH ys
   then ConsShape t1 (cpr_merge_list xs ys)
   else Leaf) ∧

  (cpr_merge_list [] ys = []) ∧
  (cpr_merge_list xs [] = []) ∧
  (cpr_merge_list (x::xs) (y::ys) = cpr_merge x y :: cpr_merge_list xs ys)
End


(* Constant tuples. A constant [Op (BlockOp (Build ps)) []] is split only if
   it is a tree whose shared parts are all immediates, so that emitting its
   fields separately allocates no more than the original [Build]. Part
   indices refer to [ps], and [pm] is [fromList ps]. *)

(* Parts that are immediate values at the word level; any other part is
   allocated on the heap. *)
Definition imm_part_def:
  (imm_part (Int i) ⇔ backend_common$small_enough_int i) ∧
  (imm_part (Con t ns) ⇔ NULL ns) ∧
  (imm_part _ ⇔ F)
End

Definition inc_refs_def:
  (inc_refs [] cnt = cnt) ∧
  (inc_refs (n::ns) cnt =
     inc_refs ns (insert n (case lookup n cnt of NONE => 1n | SOME k => k + 1) cnt))
End

(* The number of references to each part from [Con] parts. *)
Definition refcounts_def:
  (refcounts [] cnt = cnt) ∧
  (refcounts (Con t ns :: ps) cnt = refcounts ps (inc_refs ns cnt)) ∧
  (refcounts (_ :: ps) cnt = refcounts ps cnt)
End

Definition unshared_def:
  (unshared cnt (i:num) [] ⇔ T) ∧
  (unshared cnt i (p::ps) ⇔
     (imm_part p ∨ (case lookup i cnt of NONE => T | SOME k => k ≤ 1n)) ∧
     unshared cnt (i + 1) ps)
End

Definition all_below_def:
  (all_below (i:num) [] ⇔ T) ∧
  (all_below i (n::ns) ⇔ n < i ∧ all_below i ns)
End

(* Every [Con] part refers only to earlier parts. *)
Definition backward_def:
  (backward (i:num) [] ⇔ T) ∧
  (backward i (Con t ns :: ps) ⇔ all_below i ns ∧ backward (i + 1) ps) ∧
  (backward i (_ :: ps) ⇔ backward (i + 1) ps)
End

Definition str_count_def:
  (str_count [] = 0n) ∧
  (str_count (Str s :: ps) = str_count ps + 1) ∧
  (str_count (_ :: ps) = str_count ps)
End

(* The number of [Str] parts in the tree unfolded from part [r]. *)
Definition tree_strs_def:
  (tree_strs pm r =
     case lookup r pm of
       SOME (Str s) => 1n
     | SOME (Con t ns) => tree_strs_list pm r ns
     | _ => 0) ∧
  (tree_strs_list pm r [] = 0) ∧
  (tree_strs_list pm r (n::ns) =
     (if n < r then tree_strs pm n else 0) + tree_strs_list pm (r:num) ns)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<)
                (λx. case x of INL (pm,r) => (r + 1, 0)
                             | INR (pm,r,ns) => (r, LENGTH ns))’
  >> rw[pairTheory.LEX_DEF]
End

(* A [Str] part allocates a fresh reference, so there is at most one, and it
   occurs exactly once in the tree unfolded from the root: the split
   evaluates it once, into the same fresh pointer. *)
Definition build_ok_def:
  build_ok ps ⇔
    ¬NULL ps ∧ backward 0 ps ∧ unshared (refcounts ps LN) 0 ps ∧
    str_count ps ≤ 1 ∧
    tree_strs (fromList ps) (LENGTH ps - 1) = str_count ps
End

(* Unfolds every [Con] part with fields; fields are in [Op] argument order,
   the reverse of block order. *)
Definition part_shape_def:
  (part_shape pm r =
     case lookup r pm of
       SOME (Con t ns) =>
         if NULL ns then Leaf else ConsShape t (part_shape_list pm r (REVERSE ns))
     | _ => Leaf) ∧
  (part_shape_list pm r [] = []) ∧
  (part_shape_list pm r (n::ns) =
     (if n < r then part_shape pm n else Leaf) :: part_shape_list pm (r:num) ns)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<)
                (λx. case x of INL (pm,r) => (r + 1, 0)
                             | INR (pm,r,ns) => (r, LENGTH ns))’
  >> rw[pairTheory.LEX_DEF]
End

(* The parts reachable from part [r]. *)
Definition reach_def:
  (reach pm r acc =
     let acc = insert r () acc in
       case lookup r pm of
         SOME (Con t ns) => reach_list pm r ns acc
       | _ => acc) ∧
  (reach_list pm r [] acc = acc) ∧
  (reach_list pm r (n::ns) acc =
     reach_list pm (r:num) ns (if n < r then reach pm n acc else acc))
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<)
                (λx. case x of INL (pm,r,acc) => (r + 1, 0)
                             | INR (pm,r,ns,acc) => (r, LENGTH ns))’
  >> rw[pairTheory.LEX_DEF]
End

Definition renum_list_def:
  (renum_list rank [] = []) ∧
  (renum_list rank (n::ns) =
     (case lookup n rank of NONE => 0n | SOME k => k) :: renum_list rank ns)
End

Definition renum_def:
  (renum rank (Con t ns) = Con t (renum_list rank ns)) ∧
  (renum rank p = p)
End

(* Keeps the parts [i..r] that are in [keep], renumbering references by
   [rank], the new index of each kept part. *)
Definition sub_parts_def:
  sub_parts pm keep (r:num) i rank (n:num) acc =
    if r < i then REVERSE acc
    else
      case (lookup i keep, lookup i pm) of
        (SOME _, SOME p) =>
          sub_parts pm keep r (i + 1) (insert i n rank) (n + 1) (renum rank p :: acc)
      | _ => sub_parts pm keep r (i + 1) rank n acc
Termination
  WF_REL_TAC ‘measure (λ(pm,keep,r,i,rank,n,acc). r + 1 - i)’
End

(* The parts reachable from part [r], in their original order. *)
Definition sub_build_def:
  sub_build pm r = sub_parts pm (reach pm r LN) r 0 LN 0 []
End

(* Evaluates to the value of part [r] of the constant. *)
Definition part_exp_def:
  part_exp pm r =
    case lookup r pm of
      SOME (Int i) =>
        if backend_common$small_enough_int i then Op (IntOp (Const i)) []
        else Op (BlockOp (Build [Int i])) []
    | SOME (Con t ns) =>
        if NULL ns then Op (BlockOp (Cons t)) []
        else Op (BlockOp (Build (sub_build pm r))) []
    | SOME p => Op (BlockOp (Build [p])) []
    | NONE => Op (IntOp (Const 0)) []
End

Definition flatten_part_def:
  (flatten_part pm (ConsShape t shs) r =
     case lookup r pm of
       SOME (Con t' ns) =>
         if t = t' ∧ LENGTH ns = LENGTH shs
         then flatten_parts pm shs (REVERSE ns)
         else [part_exp pm r]
     | _ => [part_exp pm r]) ∧
  (flatten_part pm sh r = [part_exp pm r]) ∧
  (flatten_parts pm [] ns = []) ∧
  (flatten_parts pm shs [] = []) ∧
  (flatten_parts pm (sh::shs) (n::ns) =
     flatten_part pm sh n ++ flatten_parts pm shs ns)
Termination
  WF_REL_TAC ‘measure (λx. case x of
                             INL (pm,sh,r) => cpr_shape_size sh
                           | INR (pm,shs,ns) => list_size cpr_shape_size shs)’
End

Definition field_shape_def:
  (field_shape (Op (BlockOp (Cons t)) xs) = ConsShape t (field_shape_list xs)) /\
  (field_shape (Op (BlockOp (Build ps)) []) =
     if build_ok ps then part_shape (fromList ps) (LENGTH ps - 1) else Leaf) /\
  (field_shape _ = Leaf) /\
  (field_shape_list [] = []) /\
  (field_shape_list (x::xs) = field_shape x :: field_shape_list xs)
End

Definition shape_and_tail_def:
  (shape_and_tail fname (Var n) = (Leaf, [])) /\
  (shape_and_tail fname (If g e1 e2) =
   let (sh1, c1) = shape_and_tail fname e1;
       (sh2, c2) = shape_and_tail fname e2
   in
     (cpr_merge sh1 sh2, c1 ++ c2)) /\
  (shape_and_tail fname (Let xs b) =
     shape_and_tail fname b) /\
  (shape_and_tail fname (Raise e) = (Flexible, [])) /\
  (shape_and_tail fname (Tick e) = shape_and_tail fname e) /\
  (shape_and_tail fname (Call ts dest args hdl) =
   case hdl of
     SOME _ => (Leaf, [])
   | NONE =>
       case dest of
         SOME dname => if fname = dname then (Flexible, []) else (Flexible, [dname])
       | _ => (Leaf, [])) /\
  (shape_and_tail fname (Force loc v) = (Leaf,[])) /\
  (shape_and_tail fname (Op op xs) = (field_shape (Op op xs), [])) /\
  (shape_and_tail fname (LetCall ret ticks dest args b) =
     shape_and_tail fname b) /\
  (shape_and_tail fname (Return xs) = (Leaf, []))
End

(* The shape returned by all of the tail-called functions [fs]. [csh_map]
   maps each split function to its shape and its worker. A function that is
   not in the map, such as one defined later in the same chunk (as in mutual
   recursion), gives [Leaf]. *)
Definition tail_shape_def:
  (tail_shape _ [] = Flexible) ∧
  (tail_shape csh_map (f::fs) =
   case lookup f csh_map of
     NONE => Leaf
   | SOME (csh, wk:num) => case tail_shape csh_map fs of
                   Flexible => csh
                 | fsh => if fsh = csh then fsh else Leaf)
End

Definition shape_width_def:
  (shape_width Leaf = 1n) ∧
  (shape_width Flexible = 1) ∧
  (shape_width (ConsShape t shs) = shape_width_list shs) ∧

  (shape_width_list [] = 0) ∧
  (shape_width_list (sh::shs) = shape_width sh + shape_width_list shs)
End

(* Coarsens a shape to width at most [k] (for [k ≥ 1]), unfolding fields left
   to right while leaving one slot for each remaining field. *)
Definition cap_shape_def:
  (cap_shape k (ConsShape t shs) =
     if LENGTH shs ≤ k then ConsShape t (cap_list (k - LENGTH shs) shs)
     else Leaf) ∧
  (cap_shape k sh = sh) ∧
  (cap_list extra [] = []) ∧
  (cap_list extra (sh::shs) =
     let sh' = cap_shape (extra + 1) sh in
       sh' :: cap_list (extra + 1 - shape_width sh') shs)
Termination
  WF_REL_TAC ‘measure (λx. case x of
                             INL (k,sh) => cpr_shape_size sh
                           | INR (extra,shs) => list_size cpr_shape_size shs)’
End

(* A function with no tail calls to other functions takes the shape of its
   own tails, capped at width [k]. Otherwise it takes exactly the shape of the
   split functions it tail calls, or [Leaf] if its own tails do not refine
   that shape. *)
Definition return_shape_def:
  return_shape k csh_map fname body =
  let (sh, cs) = shape_and_tail fname body;
      csh = tail_shape csh_map cs
  in
    case (csh, sh) of
        (Flexible, _) => cap_shape k sh
      | (_, Flexible) => csh
      | _ => if sub_shape csh sh then csh else Leaf
End

Definition split_ok_def:
  split_ok sh ⇔ shape_width sh > 1
End

Definition flatten_exp_def:
  (flatten_exp Leaf e = [e]) ∧
  (flatten_exp Flexible e = [e]) ∧
  (flatten_exp (ConsShape t shs) e =
     case e of
       Op (BlockOp (Cons tag)) xs =>
         if tag = t ∧ LENGTH xs = LENGTH shs
         then flatten_list shs xs
         else [e]
     | Op (BlockOp (Build ps)) [] =>
         (case lookup (LENGTH ps - 1) (fromList ps) of
            SOME (Con tag ns) =>
              if build_ok ps ∧ tag = t ∧ LENGTH ns = LENGTH shs
              then flatten_parts (fromList ps) shs (REVERSE ns)
              else [e]
          | _ => [e])
     | _ => [e]) ∧

  (flatten_list [] xs = []) ∧
  (flatten_list shs [] = []) ∧
  (flatten_list (sh::shs) (x::xs) =
   flatten_exp sh x ++ flatten_list shs xs)
End

(* The worker returns the fields of each tail expression with [Return], and
   tail calls to split functions become tail calls to their workers. *)
Definition worker_body_def:
  (worker_body csh_map fname next sh (If g e1 e2) =
     If g (worker_body csh_map fname next sh e1) (worker_body csh_map fname next sh e2)) ∧
  (worker_body csh_map fname next sh (Let xs b) = Let xs (worker_body csh_map fname next sh b)) ∧
  (worker_body csh_map fname next sh (Tick e) = Tick (worker_body csh_map fname next sh e)) ∧
  (worker_body csh_map fname next sh (Raise e) = Raise e) ∧
  (worker_body csh_map fname next sh (LetCall ret ticks dest args b) =
     LetCall ret ticks dest args (worker_body csh_map fname next sh b)) ∧
  (worker_body csh_map fname next sh (Return xs) = Return xs) ∧
  (worker_body csh_map fname next sh (Call ts dest args hdl) =
   case hdl of
     SOME _ => Call ts dest args hdl
   | NONE =>
       case dest of
         SOME dname => (if fname = dname then TailCall (shape_width sh) ts next args
                        else case lookup dname csh_map of
                             | NONE => Call ts dest args hdl
                             | SOME (csh:cpr_shape, dwk:num) => TailCall (shape_width sh) ts dwk args)
       | _ => Call ts dest args hdl) ∧
  (worker_body csh_map fname next sh e = Return (flatten_exp sh e))
End

Definition rebuild_def:
  (rebuild i Leaf = Var i) ∧
  (rebuild i Flexible = Var i) ∧
  (rebuild i (ConsShape t shs) =
     Op (BlockOp (Cons t)) (rebuild_list i shs)) ∧

  (rebuild_list i [] = []) ∧
  (rebuild_list i (sh::shs) =
   rebuild i sh :: rebuild_list (i + shape_width sh) shs)
End


Definition make_wrapper_def:
  make_wrapper arity next sh =
    LetCall (shape_width sh) 0 next (GENLIST Var arity)
            (rebuild 0 sh)
End

Definition no_ret_def:            (* no Return anywhere *)
  (no_ret (If g e1 e2) ⇔ no_ret g ∧ no_ret e1 ∧ no_ret e2) ∧
  (no_ret (Let xs e) ⇔ no_ret_list xs ∧ no_ret e) ∧
  (no_ret (Tick e) ⇔ no_ret e) ∧
  (no_ret (Raise e) ⇔ no_ret e) ∧
  (no_ret (Return xs) ⇔ F) ∧
  (no_ret (Call ts d args hdl) ⇔
     no_ret_list args ∧ case hdl of NONE => T | SOME h => no_ret h) ∧
  (no_ret (LetCall r ts d args e) ⇔ no_ret_list args ∧ no_ret e) ∧
  (no_ret (Op op es) ⇔ no_ret_list es) ∧
  (no_ret e ⇔ T) ∧

  (no_ret_list [] ⇔ T) ∧
  (no_ret_list (x::xs) ⇔ (no_ret x ∧ no_ret_list xs))
End

Definition tail_form_def:         (* Return only in tail position *)
  (tail_form (If g e1 e2) ⇔ no_ret g ∧ tail_form e1 ∧ tail_form e2) ∧
  (tail_form (Let xs e) ⇔ no_ret_list xs ∧ tail_form e) ∧
  (tail_form (Tick e) ⇔ tail_form e) ∧
  (tail_form (LetCall r ts d args e) ⇔ no_ret_list args ∧ tail_form e) ∧
  (tail_form (Return xs) ⇔ no_ret_list xs) ∧
  (tail_form e ⇔ no_ret e)
End

Definition split_fun_def:
  split_fun k csh_map next loc arity body =
    let sh = return_shape k csh_map loc body in
      if split_ok sh ∧ tail_form body then
        SOME (worker_body csh_map loc next sh body,          (* the worker  *)
              make_wrapper arity next sh,                    (* the wrapper *)
              insert loc (sh, next) csh_map)                 (* update map  *)
      else NONE
End

Definition compile_prog_with_map_def:
  (compile_prog_with_map k csh_map next [] = ((next, csh_map), [])) ∧
  (compile_prog_with_map k csh_map next ((loc:num, arity:num, exp)::xs) =
     case split_fun k csh_map next loc arity exp of
       NONE =>
         let (st, ys) = compile_prog_with_map k csh_map next xs in
           (st, (loc, arity, exp)::ys)
     | SOME (worker, wrapper, new_map) =>
         let (st, ys) = compile_prog_with_map k new_map (next + bvl_to_bvi_namespaces) xs in
           (st, (loc, arity, wrapper)::(next, arity, worker)::ys))
End

(* [k] is the maximum number of fields a function returns unboxed; CPR is
   off for [k ≤ 1]. *)
Definition compile_prog_def:
  compile_prog k (next, csh_map) xs =
    if k ≤ 1 then ((next, csh_map), xs)
    else compile_prog_with_map k csh_map next xs
End

(* Examples; the argument of each function is [Var 0]. *)

val flat_body =
  “Op (BlockOp (Cons 0)) [Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]; Var 0]”

val nested_body =
  “If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
     (Let [Call 0 (SOME 324) [Var 0] NONE]
        (Op (BlockOp (Cons 0))
           [Op (BlockOp (Cons 0)) [Var 0; Var 0];
            Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]]))
     (Let [Call 0 (SOME 324) [Var 0] NONE]
        (Op (BlockOp (Cons 0))
           [Op (BlockOp (Cons 0))
              [Op (IntOp Add) [Var 0; Op (IntOp (Const 2)) []];
               Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]];
            Var 0]))”

val self_tail_body =
  “If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
     (Op (BlockOp (Cons 0)) [Var 0; Var 0])
     (Call 0 (SOME 1000) [Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]] NONE)”

val other_tail_body =
  “If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
     (Op (BlockOp (Cons 0)) [Var 0; Op (IntOp (Const 1)) []])
     (Call 0 (SOME 1000) [Var 0] NONE)”

val handler_body =
  “If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
     (Op (BlockOp (Cons 0)) [Var 0; Var 0])
     (Call 0 (SOME 1000) [Var 0] (SOME (Op (IntOp (Const 0)) [])))”

val let_bound_body =
  “Let [Op (BlockOp (Cons 0)) [Var 0; Var 0]] (Var 0)”

Theorem cpr_flat_example:
  compile_prog 8 (1100,LN) [(1000,1,^flat_body)] =
    ((1105,insert 1000 (ConsShape 0 [Leaf; Leaf],1100) LN),
     [(1000,1,LetCall 2 0 1100 [Var 0] (Op (BlockOp (Cons 0)) [Var 0; Var 1]));
      (1100,1,Return [Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]; Var 0])])
Proof
  EVAL_TAC
QED

Theorem cpr_nested_example:
  compile_prog 8 (1100,LN) [(1000,1,^nested_body)] =
    ((1105,insert 1000 (ConsShape 0 [ConsShape 0 [Leaf; Leaf]; Leaf],1100) LN),
     [(1000,1,
       LetCall 3 0 1100 [Var 0]
         (Op (BlockOp (Cons 0)) [Op (BlockOp (Cons 0)) [Var 0; Var 1]; Var 2]));
      (1100,1,
       If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
         (Let [Call 0 (SOME 324) [Var 0] NONE]
            (Return
               [Var 0; Var 0; Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]]))
         (Let [Call 0 (SOME 324) [Var 0] NONE]
            (Return
               [Op (IntOp Add) [Var 0; Op (IntOp (Const 2)) []];
                Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]; Var 0])))])
Proof
  EVAL_TAC
QED

(* A self tail call, and a tail call to a function split earlier, become
   tail calls to the workers. *)
Theorem cpr_tail_call_example:
  compile_prog 8 (1100,LN)
    [(1000,1,^self_tail_body); (1004,1,^other_tail_body)] =
    ((1110,insert 1004 (ConsShape 0 [Leaf; Leaf],1105)
             (insert 1000 (ConsShape 0 [Leaf; Leaf],1100) LN)),
     [(1000,1,LetCall 2 0 1100 [Var 0] (Op (BlockOp (Cons 0)) [Var 0; Var 1]));
      (1100,1,
       If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
         (Return [Var 0; Var 0])
         (TailCall 2 0 1100 [Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]]));
      (1004,1,LetCall 2 0 1105 [Var 0] (Op (BlockOp (Cons 0)) [Var 0; Var 1]));
      (1105,1,
       If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
         (Return [Var 0; Op (IntOp (Const 1)) []])
         (TailCall 2 0 1100 [Var 0]))])
Proof
  EVAL_TAC
QED

(* A call with a handler in tail position, and a tuple bound by [Let],
   prevent the split; with [k = 0] nothing changes. *)
Theorem cpr_unchanged_examples:
  compile_prog 8 (1100,LN)
    [(1000,1,^handler_body); (1004,1,^let_bound_body)] =
    ((1100,LN),[(1000,1,^handler_body); (1004,1,^let_bound_body)]) ∧
  compile_prog 0 (1100,LN) [(1000,1,^flat_body)] =
    ((1100,LN),[(1000,1,^flat_body)])
Proof
  EVAL_TAC
QED

val const_pair_body =
  “If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
     (Op (BlockOp (Build [Int 0; Int 1; Con 0 [0; 1]])) [])
     (Op (BlockOp (Cons 0)) [Var 0; Var 0])”

val const_nested_body =
  “Op (BlockOp (Build [Int 0; Con 1 [0]; Int 5; Con 0 [1; 2]])) []”

val const_str_body =
  “Op (BlockOp (Build [Str «a»; Int 1; Con 0 [0; 1]])) []”

(* Constant tuples are split into their fields; a nested tuple is split
   recursively, and a string is built on its own. *)
Theorem cpr_const_examples:
  compile_prog 8 (1100,LN)
    [(1000,1,^const_pair_body); (1004,1,^const_nested_body);
     (1008,1,^const_str_body)] =
    ((1115,insert 1008 (ConsShape 0 [Leaf; Leaf],1110)
             (insert 1004 (ConsShape 0 [Leaf; ConsShape 1 [Leaf]],1105)
               (insert 1000 (ConsShape 0 [Leaf; Leaf],1100) LN))),
     [(1000,1,LetCall 2 0 1100 [Var 0] (Op (BlockOp (Cons 0)) [Var 0; Var 1]));
      (1100,1,
       If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
         (Return [Op (IntOp (Const 1)) []; Op (IntOp (Const 0)) []])
         (Return [Var 0; Var 0]));
      (1004,1,
       LetCall 2 0 1105 [Var 0]
         (Op (BlockOp (Cons 0)) [Var 0; Op (BlockOp (Cons 1)) [Var 1]]));
      (1105,1,Return [Op (IntOp (Const 5)) []; Op (IntOp (Const 0)) []]);
      (1008,1,LetCall 2 0 1110 [Var 0] (Op (BlockOp (Cons 0)) [Var 0; Var 1]));
      (1110,1,
       Return [Op (IntOp (Const 1)) []; Op (BlockOp (Build [Str «a»])) []])])
Proof
  EVAL_TAC
QED

val const_wide_body =
  “Op (BlockOp (Build [Int 1; Int 2; Int 3; Int 4; Int 5; Con 0 [0;1;2;3;4];
                       Int 6; Int 7; Int 8; Int 9; Int 10; Con 0 [6;7;8;9;10];
                       Con 0 [5; 11]])) []”

val const_merged_body =
  “If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
     (Op (BlockOp (Build [Int 3; Int 4; Con 0 [0; 1]; Int 5; Int 6;
                          Con 0 [3; 4]; Con 0 [2; 5]])) [])
     (Op (BlockOp (Cons 0)) [Var 0; Var 0])”

(* A field left whole, by the width cap or by merging with another branch,
   is built from the parts it reaches. *)
Theorem cpr_const_coarse_examples:
  compile_prog 8 (1100,LN)
    [(1000,1,^const_wide_body); (1004,1,^const_merged_body)] =
    ((1110,insert 1004 (ConsShape 0 [Leaf; Leaf],1105)
             (insert 1000
                (ConsShape 0 [ConsShape 0 [Leaf; Leaf; Leaf; Leaf; Leaf]; Leaf],
                 1100) LN)),
     [(1000,1,
       LetCall 6 0 1100 [Var 0]
         (Op (BlockOp (Cons 0))
            [Op (BlockOp (Cons 0)) [Var 0; Var 1; Var 2; Var 3; Var 4];
             Var 5]));
      (1100,1,
       Return
         [Op (IntOp (Const 10)) []; Op (IntOp (Const 9)) [];
          Op (IntOp (Const 8)) []; Op (IntOp (Const 7)) [];
          Op (IntOp (Const 6)) [];
          Op (BlockOp (Build [Int 1; Int 2; Int 3; Int 4; Int 5;
                              Con 0 [0; 1; 2; 3; 4]])) []]);
      (1004,1,LetCall 2 0 1105 [Var 0] (Op (BlockOp (Cons 0)) [Var 0; Var 1]));
      (1105,1,
       If (Op (BlockOp (EqualConst (Int 0))) [Var 0])
         (Return
            [Op (BlockOp (Build [Int 5; Int 6; Con 0 [0; 1]])) [];
             Op (BlockOp (Build [Int 3; Int 4; Con 0 [0; 1]])) []])
         (Return [Var 0; Var 0]))])
Proof
  EVAL_TAC
QED

val two_strs_body =
  “Op (BlockOp (Build [Str «a»; Str «b»; Con 0 [0; 1]])) []”

val shared_str_body =
  “Op (BlockOp (Build [Str «a»; Con 0 [0; 0]])) []”

val shared_block_body =
  “Op (BlockOp (Build [Int 0; Con 1 [0]; Con 0 [1; 1]])) []”

(* Constants with two strings, or with a shared part on the heap, are not
   split. *)
Theorem cpr_const_unchanged_examples:
  compile_prog 8 (1100,LN)
    [(1000,1,^two_strs_body); (1004,1,^shared_str_body);
     (1008,1,^shared_block_body)] =
    ((1100,LN),
     [(1000,1,^two_strs_body); (1004,1,^shared_str_body);
      (1008,1,^shared_block_body)])
Proof
  EVAL_TAC
QED

(* bvi_inline inlines the wrapper into a (non-tail) caller. *)
Theorem cpr_inline_example:
  SND (bvi_inline$compile_prog
         (SND (compile_prog 8 (1100,LN)
                 [(1000,1,^flat_body);
                  (1004,1,Op (BlockOp (ElemAt 0))
                            [Call 0 (SOME 1000) [Var 0] NONE])]))) =
    [(1000,1,LetCall 2 0 1100 [Var 0] (Op (BlockOp (Cons 0)) [Var 0; Var 1]));
     (1100,1,Return [Op (IntOp Add) [Var 0; Op (IntOp (Const 1)) []]; Var 0]);
     (1004,1,
      Op (BlockOp (ElemAt 0))
        [Let [Var 0]
           (LetCall 2 0 1100 [Var 0] (Op (BlockOp (Cons 0)) [Var 0; Var 1]))])]
Proof
  EVAL_TAC
QED
