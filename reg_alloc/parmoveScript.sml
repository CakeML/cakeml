open preamble;

val _ = new_theory "parmove";

(* This is a formalisation of a JAR'08 paper by Rideau, Serpette, Leroy:
     Tilting at windmills with Coq: formal verification of a compilation
     algorithm for parallel moves
   http://gallium.inria.fr/~xleroy/publi/parallel-move.pdf *)

(* Non-deterministic algorithm *)

(* The state is three lists of moves:
   (to-process, being-processed, processed)
   each step (roughly) shifts some move from left to right in the state *)

(* NONE is a temporary register; real registers are SOME x.
   Alternative: specify the type as num, and use 0 as the temporary?
   Alternative: pass the temporary as an argument (quite annoying) *)

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

val windmill_def = Define `
  windmill (moves:('a # 'a) list) = ALL_DISTINCT (MAP SND moves)`;

(* The top-level parallel move compiler *)

val parmove_def = Define `
  parmove (xs:('a # 'a) list) (temp:'a) = xs (* TODO *)`

val _ = export_theory();
