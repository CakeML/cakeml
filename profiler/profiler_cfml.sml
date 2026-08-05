(*
  Shadows bindings to enable profiling of some CFML tactics.
*)
structure profiler_cfml =
struct

open Abbrev; (* for tactic type *)
local open cfTacticsLib in end;

val xpull : tactic = Profiler.profile_tac "xpull" cfTacticsLib.xpull
val xmatch : tactic = Profiler.profile_tac "xmatch" cfTacticsLib.xmatch
val xsimpl : tactic = Profiler.profile_tac "xsimpl" cfTacticsLib.xsimpl
val xapp : tactic = Profiler.profile_tac "xapp" cfTacticsLib.xapp
val xif : tactic = Profiler.profile_tac "xif" cfTacticsLib.xif
val xcon : tactic = Profiler.profile_tac "xcon" cfTacticsLib.xcon
val xlog : tactic = Profiler.profile_tac "xlog" cfTacticsLib.xlog
val xlet_auto : tactic = Profiler.profile_tac "xlet_auto" cfLetAutoLib.xlet_auto
fun xlet (q: term quotation) : tactic =
  Profiler.profile_tac "xlet" (cfTacticsLib.xlet q)
fun xcf_with_def thm : tactic =
    Profiler.profile_tac "xcf_with_def" (xcf.xcf_with_def thm)

end
