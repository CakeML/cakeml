open preamble dataLangTheory;

val _ = new_theory "data_cse";

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

val _ = monadsyntax.temp_add_monadsyntax();
val _ = temp_overload_on ("monad_bind", ``OPTION_BIND``);

fun num_setPrinter  Gs B sys ppfns (pg,lg,rg) d t =
  if can (find_term (fn x => is_var x orelse is_abs x)) t
  then raise term_pp_types.UserPP_Failed
  else
  let val a = EVAL ``MAP FST (toAList ^t)``
      val t = rhs (concl a)
  in
      sys{gravs = (pg,pg,pg), depth = d, binderp = false} t
  end;
Parse.temp_add_user_printer ("spTree_printer", ``_: num_set``, num_setPrinter);


val is_pure_def = Define `
  (is_pure SetGlobalsPtr = F) /\
  (is_pure Ref = F) /\
  (is_pure (RefByte _) = F) /\
  (is_pure RefArray = F) /\
  (is_pure Update = F) /\
  (is_pure UpdateByte = F) /\
  (is_pure FromListByte = F) /\
  (is_pure (CopyByte _) = F) /\
  (is_pure (String _) = F) /\
  (is_pure (Cons _) = F) /\
  (is_pure (ConsExtend _) = F) /\
  (is_pure (FFI _) = F) /\
  (is_pure (FromList _) = F) /\
  (is_pure Add = F) /\
  (is_pure Sub = F) /\
  (is_pure Mult = F) /\
  (is_pure Div = F) /\
  (is_pure Mod = F) /\
  (is_pure Less = F) /\
  (is_pure LessEq = F) /\
  (is_pure Equal = F) /\
  (is_pure (WordOp W64 _) = F) /\
  (is_pure (WordShift W64 _ _) = F) /\
  (is_pure WordFromInt = F) /\
  (is_pure WordToInt = F) /\
  (is_pure (FP_uop _) = F) /\
  (is_pure (FP_bop _) = F) /\
  (is_pure _ = T)`

val is_cheap_op = Define `
(is_cheap_op ((Const _) : op) = T) /\
(is_cheap_op (_ : op) = F)`

val is_pure_pmatch = Q.store_thm("is_pure_pmatch",`!op.
  is_pure op =
    case op of
      SetGlobalsPtr => F
    | Ref => F
    | RefByte _ => F
    | RefArray => F
    | Update => F
    | UpdateByte => F
    | FromListByte => F
    | CopyByte _ => F
    | String _ => F
    | Cons _ => F
    | ConsExtend _ => F
    | FFI _ => F
    | FromList _ => F
    | Add => F
    | Sub => F
    | Mult => F
    | Div => F
    | Mod => F
    | Less => F
    | LessEq => F
    | Equal => F
    | WordOp W64 _ => F
    | WordShift W64 _ _ => F
    | WordFromInt => F
    | WordToInt => F
    | FP_uop _ => F
    | FP_bop _ => F
    | _ => T`,
  rpt strip_tac
  >> CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  >> every_case_tac >> fs[is_pure_def]);

(* Overview: It keeps track of the computed pure expressions in scope. When such
an expression is detected furhter in the program it is replaced by the variable
in which it was stored *)

(* Details:
The caches needs to implement the following:
- empty_cache : cache
- cache_invalidate : cache -> num -> cache
Removes `n` from its entry (if present). Then, if it has a twin `t`,
replaces all occurrences of `n` by `t` in the cache.
Otherwise removes all expressions that contain `n`.

- invalidate_all_but : cache -> num_set -> cache
Invalidates all the variables but the ones in the given set.

- memoize : cache -> num -> (op, vs) -> cache
Inserts the assignment into the cache, i.e. it appends the `n` to the entry pointed by `(op, vs)`.

Algorithm:
When we find an assignment `a@(Assign v op vs live)`:
- Remove every variable that is not in live from the cache.
- Invalidate `v`, i.e. remove all expressions from the cache that contain `v`.
- If the `op` is not pure, return `a`.
- Lookup whether an equivalent expression is in the cache. If present associated
with some variable `n`, replace the assignment by `Move v n`.
- Add the association (v, a) to the cache.

When we find `Move n m`:
Append `m` to the same entry as `n`.

When we find `call _ _ _ _` ?? if the first argument is NONE, it will not
return. if it is SOME (n, live), then it cuts out everything that is not in live
and assigns something "impure" to `n`
 *)

(* MAP UTILS *)
val empty_map = Define `empty_map = []`

val map_alter = Define `
(map_alter f k [] = dtcase f NONE of
                      | NONE => []
                      | (SOME v) => [(k, v)]) /\
(map_alter f k ((k1, v1)::hs) =
 if k = k1 then
     (dtcase f (SOME v1) of
        | NONE => hs
        | (SOME newval) => (k1, newval)::hs)
 else ((k1, v1)::map_alter f k hs))`

val map_update = Define `
map_update f = map_alter (OPTION_MAP f)`

val map_combine = Define `
map_combine f = map_alter (SOME o f)`

val map_insert = Define `
map_insert k v = map_update (\_. SOME v) k`

val map_fmap = Define `
(map_fmap f [] = []) /\
(map_fmap f ((k, v)::hs) = (k, f v)::map_fmap f hs)`

val num_set_toList = Define`
num_set_toList = MAP FST o toAList`

val map_maybe = Define`
(map_maybe f [] = []) /\
(map_maybe f (x::xs) =
let ts = map_maybe f xs in
option_CASE (f x) ts (\sx. sx::ts))
`

val num_set_contains = Define `
num_set_contains k s = IS_SOME (lookup k s)`

(* TODO there must be a faster way of doing this *)
val num_set_head_may = Define `
num_set_head_may sp = dtcase num_set_toList sp of
                         | (x::_) => SOME x : num option
                         | _ => NONE`
val _ = Datatype `
cache = Cache ((op # ((num list # num_set) list)) list)`

val empty_cache = Define`
empty_cache = Cache [] : cache`

(* Auxiliary function for invalidate. Removes `n` from its twin set and returns
 a twin, if any. `n` is assumed to be in at most one twin set. Note that the
 arguments are untouched, therefore it is necessary to adjust occurrences of `n`
 in the arguments afterwards. Returns (maybe twin, T <=> `n` was found, updated
 twin sets) *)

val pop_var_find_twin = Define`
(pop_var_find_twin _ [] = (NONE, F, [])) /\
(pop_var_find_twin n ((args, twin_set) :: ts) =
    if IS_SOME (lookup n twin_set)
    then (
        let twins1 = delete n twin_set in
        let twin = num_set_head_may twins1 in
            if isEmpty twins1
            then (twin, T, ts)
            else (twin, T, (args, twins1)::ts)
    )
    else (\ (a, b, c). (a, b, (args, twin_set)::c)) (pop_var_find_twin n ts))`

val pop_var_find_twin2 = Define `
(pop_var_find_twin2 n [] = (NONE, [])) /\
(pop_var_find_twin2 n ((op, ls)::hs) =
 dtcase pop_var_find_twin n ls of
   | (twin, T, []) => (twin, hs)
   | (twin, T, ls1) => (twin, (op, ls1)::hs)
   | (_, F, ls1) => dtcase pop_var_find_twin2 n hs of
                        | (twin, hs1) => (twin, (op, ls1)::hs1))`

val replace_var_twin = Define `
(replace_var_twin NONE n ts =
 FILTER (\ (args, twins). ~(MEM n args)) ts) /\
(replace_var_twin (SOME twin) n (ts : (num list # num_set) list) =
 MAP (\ (args, twins). (MAP (\var. if var = n then twin else var) args, twins)) ts)`


(* Removes `n` from its entry (if present). Then, if it has a twin `t`, replaces
all occurrences of `n` by `t` in the cache. Otherwise removes all expressions
that contain `n`. *)
val cache_invalidate = Define`
cache_invalidate (Cache entries : cache) (n : num) =
let (twin, entries1) = pop_var_find_twin2 n entries in
    Cache
          (map_maybe (\ (op, es).
                        let r = replace_var_twin twin n es in
                            if NULL r then NONE
                            else SOME (op, r)) entries1)`

val cache_entries = Define`
cache_entries (Cache entries) = entries`

val cache_invalidate_simple = Define `
cache_invalidate_simple (Cache entries) n = Cache
    (map_maybe (\ (op, aargs).
      dtcase map_maybe (\ (args, twins).
           if MEM n args
           then NONE
           else (let twins1 = delete n twins in
                if isEmpty twins1
                then NONE
                else (SOME (args, twins1)))) aargs
      of
        | [] => NONE
        | aargs1 => SOME (op, aargs1)) entries)`

val cache_memoize2 = Define`
(cache_memoize2 n NONE = insert n () LN ) /\
(cache_memoize2 n (SOME twinset) = insert n () twinset)`

val cache_memoize1 = Define`
(cache_memoize1 n args NONE = [(args, insert n () LN)] ) /\
(cache_memoize1 n args (SOME entries) = map_combine (cache_memoize2 n) args entries)`

(* memoizes `n = op args` *)
val cache_memoize = Define`
cache_memoize (Cache entries) (n:num) (op:op) (args:num list) =
Cache (map_combine (cache_memoize1 n args) op entries)`

(* memoizes `n = m` *)
(* TODO Since `n` must appear only once, this should be made more efficient *)
val cache_memoize_move = Define`
cache_memoize_move (Cache entries) n m =
Cache
    (map_fmap (map_fmap
                  (\twins. if IS_SOME (lookup m twins)
                           then insert n () twins else twins)) entries)`

(* The set of all variables in the cache *)
val cache_varset = Define`
cache_varset (Cache entries) =
    FOLDR (\ (op, aargs) ac.
             FOLDR (\ (args, twins) ac1.
                      FOLDR (\arg ac2.
                              insert arg () ac2) (union ac1 twins) args) ac aargs)
          LN entries`

val cache_cut_out_not_live = Define`
cache_cut_out_not_live cache live =
    FOLDR (\n ac. cache_invalidate ac n) cache
          (num_set_toList (difference (cache_varset cache) live))`

(* Returns a variable that contains the result of the given expression *)
val cache_lookup = Define`
cache_lookup (Cache entries) op args =
do
    m <- ALOOKUP entries op;
    x <- ALOOKUP m args;
    num_set_head_may x od`

(* val cache_intersect_entries = Define` *)
(* cache_intersect_entries (a : (op, (num list, num_set) alist) alist) b = *)
(*     map_intersect (\x y . map_intersect inter x y) a b` *)
val map_intersect = Define `
(map_intersect f [] y = []) /\
(map_intersect f ((ka, va)::xs) y =
 dtcase ALOOKUP y ka of
   | NONE => map_intersect f xs y
   | SOME vb => (ka, f va vb) :: map_intersect f xs y)`

val cache_intersect_entries = Define`
cache_intersect_entries =
    map_intersect (map_intersect inter)`

val cache_intersect = Define `
cache_intersect (Cache entries1) (Cache entries2) =
Cache (cache_intersect_entries entries1 entries2)`

val compile_def = Define`
(compile Skip c = (Skip, c)) /\
(compile (Return n) c = (Return n, c)) /\
(compile (Raise n) c = (Raise n, c)) /\
(compile (Move n1 n2) c = (Move n1 n2, cache_memoize_move c n1 n2)) /\
(compile (Seq p1 p2) c =
 let (p1c, c1) = compile p1 c in
 let (p2c, c2) = compile p2 c1 in
     (Seq p1c p2c, c2)) /\
(compile Tick c = (Tick, c)) /\
(compile (MakeSpace k live) c =
 (MakeSpace k live, cache_cut_out_not_live c live)) /\
(compile (Assign n op args live) c0 =
 let c1 = option_CASE live c0 (cache_cut_out_not_live c0) in
 let c2 = cache_invalidate c1 n in
     if ~ (is_pure op) then (Assign n op args live, c2) else (
     if is_cheap_op op
     then (Assign n op args live, cache_memoize c2 n op args)
     else ((dtcase cache_lookup c2 op args:num option of
             | NONE => (Assign n op args live,
                        if MEM n args then c2
                        else cache_memoize c2 n op args)
             | (SOME m) => (Move n m, cache_memoize_move c2 n m)
          ))
 )) /\
(compile (If cond p1 p2) c =
 let (p1c, c1) = compile p1 c in
 let (p2c, c2) = compile p2 c in
     (If cond p1c p2c, cache_intersect c1 c2)) /\
(compile (Call NONE dest vs handler) c = (Call NONE dest vs handler, c)) /\
(compile (Call (SOME (n, live)) dest vs NONE) c =
 let c1 = cache_invalidate c n in
     (Call (SOME (n, live)) dest vs NONE, cache_cut_out_not_live c1 live)) /\
(compile (Call (SOME (n, live)) dest args (SOME (m, p))) c =
 let c1 = cache_invalidate c n in
 let l2 = cache_cut_out_not_live c1 live in
 let (pc, l3) = compile p (cache_invalidate c m) in
     (Call (SOME (n, live)) dest args (SOME (m, pc)), cache_intersect l2 l3)
)`

(* Holmake in benchmarks *)

(* computeLib.add_funs [OPTION_BIND_def]; *)

val p1 = `` (compile
(FOLDR Seq Skip
       [
         Assign 0 (Const 1) [] NONE (* a = 1; *)
       ; Assign 1 (Const 2) [] NONE (* b = 2 *)
       ; Assign 2 Greater [0; 1] NONE (* c = a > b *)
       ; Assign 3 Greater [0; 1] NONE (* d = a > b *)
       ; Assign 4 (Const 1) [] NONE (* e = 1 *)
       ; Assign 5 Greater [4; 1] NONE   (* f = e > b *)
       ; Assign 6 (Const 2) [] NONE (* g = 2 *)
       ; Assign 1 (Const 0) [] NONE (* b = 0 *)
       ; Assign 3 Greater [0; 6] NONE   (* d = a > g *)
       ; Assign 6 (Const 4) [] NONE (* g = 4 *)
       ; Assign 6 Greater [6; 6] NONE (* g = g > g *)
       ; Assign 0 Greater [6; 6] NONE (* a = g > g *)
       ; Assign 1 Greater [6; 6] NONE (* b = g > g *)
])
empty_cache)
``
val p1c = EVAL p1

val _ = export_theory();
