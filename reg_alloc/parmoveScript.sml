open preamble;

val _ = new_theory "parmove";

(* TODO: move *)

val NULL_APPEND = Q.store_thm("NULL_APPEND[simp]",
  `NULL (l1 ++ l2) ⇔ NULL l1 ∧ NULL l2`,
  simp[NULL_LENGTH]);

(* -- *)

(* This is a formalisation of a JAR'08 paper by Rideau, Serpette, Leroy:
     Tilting at windmills with Coq: formal verification of a compilation
     algorithm for parallel moves
   http://gallium.inria.fr/~xleroy/publi/parallel-move.pdf *)

(* Non-deterministic algorithm *)

(* The state is three lists of moves:
   (to-process, being-processed, processed)
   each step (roughly) shifts some move from left to right in the state *)

(* NONE is a temporary register; real registers are SOME x. *)

val _ = add_infix("\226\150\183",450,NONASSOC);

val _ = overload_on("NoRead",``λμ dn. ¬MEM dn (MAP FST μ)``);

val (step_rules,step_ind,step_cases) = xHol_reln"step"`
  ((μ1++[(r,r)]++μ2,σ,τ) ▷ (μ1++μ2,σ,τ)) ∧
  ((μ1++[(s,d)]++μ2,[],τ) ▷ (μ1++μ2,[(s,d)],τ)) ∧
  ((μ1++[(d,r)]++μ2,[(s,d)]++σ,τ) ▷ (μ1++μ2,[(d,r);(s,d)]++σ,τ)) ∧
  ((μ,σ++[(s,d)],τ) ▷ (μ,σ++[(NONE,d)],[(s,NONE)]++τ)) ∧
  (NoRead μ dn ∧ dn ≠ s0 ⇒
   (μ,[(sn,dn)]++σ++[(s0,d0)],τ) ▷ (μ,σ++[(s0,d0)],[(sn,dn)]++τ)) ∧
  (NoRead μ d ⇒
   (μ,[(s,d)],τ) ▷ (μ,[],[(s,d)]++τ))`;

(* invariant on states *)

val windmill_def = Define `
  windmill (moves:('a # 'a) list) = ALL_DISTINCT (MAP SND moves)`;

val path_def = Define`
  (path [] ⇔ T) ∧ (path [_] ⇔ T) ∧
  (path ((b',c)::(a,b)::p) ⇔
     (b = b') ∧ path ((a,b)::p))`;
val _ = export_rewrites["path_def"];

val path_change_start = Q.store_thm("path_change_start",
  `∀y z x. path (SNOC x y) ∧ (SND x = SND z) ⇒ path (SNOC z y)`,
  simp[SNOC_APPEND] >>
  Induct >> simp[] >>
  Cases >> simp[] >>
  Cases_on`y`>>fs[] >- (
    Cases >> Cases >> simp[] >> rw[] ) >>
  Cases_on`h`>>simp[] >> rw[] >> metis_tac[])

val path_tail = Q.store_thm("path_tail",
  `∀t h. path (h::t) ⇒ path t`,
  Induct >> simp[] >>
  Cases >> Cases >> simp[])

val wf_def = xDefine"wf"`
  ⊢ (μ,σ,τ) ⇔
    windmill (μ++σ) ∧
    EVERY IS_SOME (MAP FST μ) ∧
    EVERY IS_SOME (MAP SND μ) ∧
    (¬NULL σ ⇒ EVERY IS_SOME (MAP FST (FRONT σ))) ∧
    EVERY IS_SOME (MAP SND σ) ∧
    path σ`;

val wf_init = Q.store_thm("wf_init",
  `windmill μ ∧
   EVERY IS_SOME (MAP FST μ) ∧
   EVERY IS_SOME (MAP SND μ) ⇒
   ⊢ (μ,[],[])`,
  rw[wf_def,path_def])

(* The invariant is preserved *)

val wf_step = Q.store_thm("wf_step",
  `∀s1 s2. s1 ▷ s2 ⇒ ⊢ s1 ⇒ ⊢ s2`,
  ho_match_mp_tac step_ind >> rw[] >>
  fs[wf_def,windmill_def,ALL_DISTINCT_APPEND] >>
  fs[GSYM SNOC_APPEND,FRONT_DEF] >>
  TRY (match_mp_tac path_change_start) >>
  metis_tac[SND,path_tail]);

(* The top-level parallel move compiler *)

val parmove_def = Define `
  parmove (xs:('a # 'a) list) (temp:'a) = xs (* TODO *)`

val _ = export_theory();
