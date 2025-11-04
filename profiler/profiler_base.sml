(*
  Shadows bindings to enable profiling of definitions, proofs and some tactics.
*)
structure profiler_base =
struct

open Abbrev; (* for tactic type *)

structure TotalDefn =
struct
open TotalDefn
(* Profile Definition *)
val old_qDefine = TotalDefn.qDefine
fun qDefine stem q tacopt =
  Profiler.profile stem (fn () => old_qDefine stem q tacopt)
end

structure Q =
struct
open Q
(* Profile Theorem .. Proof .. QED *)
val old_store_thm_at = Q.store_thm_at
fun store_thm_at loc (s,q,t) =
  Profiler.profile s (fn () => old_store_thm_at loc (s,q,t))
end

(* Tactic combinators *)
fun op >- (tac1: tactic, tac2: tactic) : tactic =
  op Tactical.>- (tac1, Profiler.profile_tac ">-" tac2)
fun op by (q, tac: tactic) =
  op BasicProvers.by (q, Profiler.profile_tac "by" tac)

(* Simplifiers *)
fun rw thms : tactic = Profiler.profile_tac "rw" (bossLib.rw thms)
fun fs thms : tactic = Profiler.profile_tac "fs" (bossLib.fs thms)
fun rfs thms : tactic = Profiler.profile_tac "rfs" (bossLib.rfs thms)
fun simp thms : tactic = Profiler.profile_tac "simp" (bossLib.simp thms)

end
