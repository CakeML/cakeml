(*
  Model of floating-point optimizations
*)
Theory fpOpt
Ancestors
  misc fpValTree

val _ = numLib.temp_prefer_num();

(*
  Definition of the fp_pattern language for Icing optimizations
*)

Datatype:
 fp_pat =
       Word word64
     | PatVar num
     | Unop fp_uop fp_pat
     | Binop fp_bop fp_pat fp_pat
     | Terop fp_top fp_pat fp_pat fp_pat
     | Cmp fp_cmp fp_pat fp_pat
     | Optimise fp_opt fp_pat
End

(* Substitutions are maps (paired lists) from numbers to 'a *)
Type subst = ``: (num # 'v) list``

Definition substLookup_def:
 substLookup [] n=  NONE ∧
 substLookup ((m, v)::s) n = (if (m = n) then SOME v else substLookup s n)
End

Definition substUpdate_def:
 substUpdate n v1 s=
   (case s of
     [] => NONE
    | (s1::sN) =>
        (case s1 of
           (m,v2) =>
             if (n = m) then SOME ((n,v1)::sN)
             else
               (case (substUpdate n v1 sN) of
                  NONE => NONE
                | SOME sNew => SOME ((m,v2)::sNew))))
End

Definition substAdd_def:
  substAdd n v s =
    (case (substUpdate n v s) of
      SOME sNew => sNew
     | NONE => (n,v)::s)
End

(* Matching a fp_pattern with the top-level of a value tree,
  if a matching exists an option with a substitution is returned.
  The matcher takes an additional substituion as argument to make sure
  that we do not double match a fp_pattern to different expressions
 *)
Definition matchWordTree_def:
  matchWordTree (Word w1) (Fp_const w2) s =
    (if (w1 = w2) then SOME s else NONE) ∧
  matchWordTree (PatVar n) v s =
    (case substLookup s n of
       SOME v1 => if v1 = v then SOME s else NONE
     | NONE => SOME (substAdd n v s)) ∧
  matchWordTree (Unop op1 p) (Fp_uop op2 v) s =
    (if (op1 = op2) then matchWordTree p v s
     else NONE) ∧
  matchWordTree (Binop b1 p1 p2) (Fp_bop b2 v1 v2) s =
    (if (b1 = b2) then
       (case matchWordTree p1 v1 s of
          NONE => NONE
        | SOME s1 => matchWordTree p2 v2 s1
       )
     else NONE) ∧
  matchWordTree (Terop t1 p1 p2 p3) (Fp_top t2 v1 v2 v3) s =
  (if (t1 = t2) then
     (case matchWordTree p1 v1 s of
        NONE => NONE
      | SOME s1 =>
          (case matchWordTree p2 v2 s1 of
             NONE => NONE
           | SOME s2 => matchWordTree p3 v3 s2))
   else NONE) ∧
  matchWordTree (Optimise fp_opt1 p) (Fp_wopt fp_opt2 v) s =
    (if fp_opt1 = fp_opt2 then matchWordTree p v s else NONE) ∧
  matchWordTree _ _ s =  NONE
End

Definition matchBoolTree_def:
  matchBoolTree (Optimise fp_opt1 p) (Fp_bopt fp_opt2 v) s =
    (if fp_opt1 = fp_opt2 then (matchBoolTree p v s) else NONE) ∧
  matchBoolTree (Cmp cmp1 p1 p2) (Fp_cmp cmp2 v1 v2) s =
    (if (cmp1 = cmp2) then
       (case matchWordTree p1 v1 s of
          NONE => NONE
        | SOME s1 => matchWordTree p2 v2 s1)
     else NONE) ∧
  matchBoolTree _ _ _ =  NONE
End

(* Instantiate a given fp_pattern with a substitution into a value tree *)
Definition instWordTree_def:
  instWordTree (Word w) s = (SOME (Fp_const w)) ∧
  instWordTree (PatVar n) s = (substLookup s n) ∧
  instWordTree (Unop u p) s =
    (case instWordTree p s of
       NONE => NONE
     | SOME v => SOME (Fp_uop u v)) ∧
  instWordTree (Binop op p1 p2) s =
    (case (instWordTree p1 s, instWordTree p2 s) of
       (SOME v1, SOME v2) => SOME (Fp_bop op v1 v2)
     | (_, _) => NONE) ∧
  instWordTree (Terop op p1 p2 p3) s =
    (case (instWordTree p1 s, instWordTree p2 s , instWordTree p3 s) of
       (SOME v1, SOME v2, SOME v3) => SOME (Fp_top op v1 v2 v3)
     | (_, _, _) => NONE) ∧
  instWordTree (Optimise fp_opt p) s =
    (case instWordTree p s of
       NONE => NONE
     | SOME v => SOME (Fp_wopt fp_opt v)) ∧
  instWordTree _ _=  NONE
End

Definition instBoolTree_def:
  instBoolTree (Optimise fp_opt p) s =
    (case instBoolTree p s of
       NONE => NONE
     | SOME v => SOME (Fp_bopt fp_opt v)) ∧
  instBoolTree (Cmp cmp p1 p2) s =
    (case (instWordTree p1 s, instWordTree p2 s) of
       (SOME v1, SOME v2) => SOME (Fp_cmp cmp v1 v2)
     | (_, _) => NONE) ∧
  instBoolTree _ _ =  NONE
End

(* Define a floating-point rewrite as a pair of a source and target fp_pattern *)
Type fp_rw = ``: (fp_pat # fp_pat)``

(** Rewriting on value trees is done in the semantics by picking a fp_path
  that walks down the value tree structure and then applies the rewrite in place
  if it matches **)

(* Datatype for fp_paths into a value tree. Here is the leaf node meaning that the
  rewrite should be applied *)
Datatype:
  fp_path = Left fp_path | Right fp_path | Center fp_path | Here
End

(* Function rwFp_pathValTree b rw p v recurses through value tree v using fp_path p
  until p = Here or no further recursion is possible because of a mismatch.
  In case of a mismatch the function simply returns Nothing. *)
Definition rwFp_pathWordTree_def:
 rwFp_pathWordTree rw Here v=
   (let (lhs, rhs) = rw in
      (case matchWordTree lhs v [] of
         NONE => NONE
       | SOME s => instWordTree rhs s)) ∧
 rwFp_pathWordTree rw (Left p) (Fp_bop op v1 v2) =
   (OPTION_MAP (\ v1 .  Fp_bop op v1 v2) (rwFp_pathWordTree rw p v1)) ∧
 rwFp_pathWordTree rw (Right p) (Fp_bop op v1 v2) =
   (OPTION_MAP (\ v2 .  Fp_bop op v1 v2) (rwFp_pathWordTree rw p v2)) ∧
 rwFp_pathWordTree rw (Center p) (Fp_uop op v1) =
   (OPTION_MAP (\ v .  Fp_uop op v) (rwFp_pathWordTree rw p v1)) ∧
 rwFp_pathWordTree rw (Left p) (Fp_top op v1 v2 v3) =
   (OPTION_MAP (\ v1 .  Fp_top op v1 v2 v3) (rwFp_pathWordTree rw p v1)) ∧
 rwFp_pathWordTree rw (Center p) (Fp_top op v1 v2 v3) =
   (OPTION_MAP (\ v2 .  Fp_top op v1 v2 v3) (rwFp_pathWordTree rw p v2)) ∧
 rwFp_pathWordTree rw (Right p) (Fp_top op v1 v2 v3) =
   (OPTION_MAP (\ v3 .  Fp_top op v1 v2 v3) (rwFp_pathWordTree rw p v3)) ∧
 rwFp_pathWordTree rw (Center p) (Fp_wopt fp_opt v) =
   (OPTION_MAP (\ v .  Fp_wopt fp_opt v) (rwFp_pathWordTree rw p v)) ∧
 rwFp_pathWordTree _ _ _=  NONE
End

Definition rwFp_pathBoolTree_def:
  rwFp_pathBoolTree rw Here v =
    (let (lhs, rhs) = rw in
       (case matchBoolTree lhs v [] of
          NONE => NONE
        | SOME s => instBoolTree rhs s)) ∧
  rwFp_pathBoolTree rw (Center p) (Fp_bopt fp_opt v) =
    (OPTION_MAP (\ v .  Fp_bopt fp_opt v) (rwFp_pathBoolTree rw p v)) ∧
  rwFp_pathBoolTree rw (Left p) (Fp_cmp cmp v1 v2) =
    (OPTION_MAP (\ v1 .  Fp_cmp cmp v1 v2) (rwFp_pathWordTree rw p v1)) ∧
  rwFp_pathBoolTree rw (Right p) (Fp_cmp cmp v1 v2) =
    (OPTION_MAP (\ v2 .  Fp_cmp cmp v1 v2) (rwFp_pathWordTree rw p v2)) ∧
  rwFp_pathBoolTree _ _ _=  NONE
End

(* Datatype holding a single rewrite application in the form of a fp_path into the
  value tree and a number giving the index of the rewrite to be used *)
Datatype:
  rewrite_app = RewriteApp fp_path num
End

Definition nth_def:
 nth [] n=  NONE ∧
 nth (x::xs) n =
   (if (n =( 0 : num)) then NONE
    else if (n =( 1 : num)) then SOME x
    else nth xs (n -( 1 : num)))
End

(* rwAllValTree rwApps canOpt rws v applies all the rewrite_app's in rwApps to
    value tree v using rwFp_pathValTree *)
Definition rwAllWordTree_def:
 rwAllWordTree [] rws v =  (SOME v) ∧
 rwAllWordTree ((RewriteApp p n)::rs) rws v =
  (case nth rws n of
     NONE => NONE
   | SOME rw =>
       (case rwFp_pathWordTree rw p v of
          NONE => NONE
        | SOME vNew => rwAllWordTree rs rws vNew))
End

Definition rwAllBoolTree_def:
 rwAllBoolTree [] rws v =  (SOME v) ∧
 rwAllBoolTree ((RewriteApp p n)::rs) rws v =
   (case nth rws n of
      NONE => NONE
    | SOME rw =>
        (case rwFp_pathBoolTree rw p v of
           NONE => NONE
         | SOME vNew => rwAllBoolTree rs rws vNew))
End

(*val no_fp_opts : nat -> list rewrite_app*)
Definition no_fp_opts_def:
 no_fp_opts (n:num) = []
End

