(*
   General-purpose option lemmas (OPTION_MAP, OPTION_BIND, option_le,
   OPT_MMAP, option_fold, etc.) used throughout the CakeML development.
*)
Theory optionLemmas
Ancestors
  listLemmas option
  list pred_set
Libs
  boolSimps mp_then dep_rewrite BasicProvers

val _ = numLib.temp_prefer_num();

(* used just once; better as
     transitive R ==> transitive (OPTREL R)
   or that with transitive expanded out *)
Theorem OPTREL_trans:
   !R x y z. (!a b c. (x = SOME a) /\ (y = SOME b) /\ (z = SOME c) /\ R a b /\ R b c ==> R a c)
    /\ OPTREL R x y /\ OPTREL R y z ==> OPTREL R x z
Proof
  srw_tac[][optionTheory.OPTREL_def]
QED

(* never used *)
Theorem IN_option_rwt:
 (x IN case opt of NONE => {} | SOME y => Q y) <=>
  (?y. (opt = SOME y) /\ x IN Q y)
Proof
Cases_on `opt` >> srw_tac[][EQ_IMP_THM]
QED

(* never used *)
Theorem IN_option_rwt2:
 x IN option_CASE opt {} s <=> ?y. (opt = SOME y) /\ x IN s y
Proof
Cases_on `opt` >> srw_tac[][]
QED

Theorem OPT_MMAP_MAP_o:
   !ls. OPT_MMAP f (MAP g ls) = OPT_MMAP (f o g) ls
Proof
  Induct \\ rw[OPT_MMAP_def]
QED

Theorem OPT_MMAP_SOME[simp]:
   OPT_MMAP SOME ls = SOME ls
Proof
  Induct_on`ls` \\ rw[OPT_MMAP_def]
QED

Theorem OPT_MMAP_CONG[defncong]:
   !l1 l2 f f'.
     (l1 = l2) /\
     (!x. MEM x l2 ==> (f x = f' x))
     ==> (OPT_MMAP f l1 = OPT_MMAP f' l2)
Proof
  Induct \\ rw[OPT_MMAP_def] \\ rw[OPT_MMAP_def] \\
  Cases_on`f' h` \\ rw[] \\ fs[] \\ metis_tac[]
QED

Theorem IMP_OPT_MMAP_EQ:
   !l1 l2. (MAP f1 l1 = MAP f2 l2) ==> (OPT_MMAP f1 l1 = OPT_MMAP f2 l2)
Proof
  Induct \\ rw[OPT_MMAP_def] \\ Cases_on`l2` \\ fs[OPT_MMAP_def] \\
  Cases_on`f2 h'` \\ fs[] \\ metis_tac[]
QED

Theorem OPTION_MAP_I[simp]:
   OPTION_MAP I x = x
Proof
  Cases_on`x` \\ rw[]
QED

(* should be made an iff in conclusion *)
Theorem OPTION_MAP_INJ:
   (!x y. f x = f y ==> x = y)
   ==> !o1 o2.
     OPTION_MAP f o1 = OPTION_MAP f o2 ==> o1 = o2
Proof
  strip_tac \\ Cases \\ Cases \\ simp[]
QED

Theorem OPTION_CHOICE_EQUALS_OPTION:
   !(x:'a option) y z. (OPTION_CHOICE x y = SOME z) <=>
                       ((x = SOME z) \/ ((x = NONE) /\ (y = SOME z)))
Proof
 rw[] \\ Cases_on `x` \\ Cases_on `y` \\ fs[]
QED

Theorem FOLDL_OPTION_CHOICE_EQ_SOME_IMP_MEM:
   FOLDL OPTION_CHOICE x ls = SOME y ==> MEM (SOME y) (x::ls)
Proof
  qid_spec_tac`x` \\ Induct_on`ls` \\ rw[] \\
  res_tac \\ fs[] \\ Cases_on`x` \\ fs[]
QED
