(*
  Synthetic benchmark isolating Definition.new_definition cost.
  Creates N constants c_0, c_1, ..., c_{N-1} with:
     c_0 = T, c_1 = T, c_{i+2} = c_i /\ c_{i+1}
  Each definition is a simple equation with a fresh LHS variable,
  matching the shape we use in ml_progLib's define_fresh_tree.
  Depends only on bool so the benchmark can build with a minimal theory
  graph — useful for later instrumenting HOL4's kernel directly.
*)

Theory bench_newdef

Ancestors
  bool

Libs
  preamble

val N = 1500

fun mk_name i = "c_" ^ Int.toString i

(* Cache for the defined constants so we don't pay O(sig) prim_mk_const
   per lookup; filled in as we define each c_i. *)
val const_arr : term array = Array.array (N, T)

fun mk_rhs 0 = T
  | mk_rhs 1 = T
  | mk_rhs i = mk_conj (Array.sub (const_arr, i-2),
                        Array.sub (const_arr, i-1))

val _ = print "\n=== bench_newdef: Definition.new_definition microbench ===\n"

(* Pre-populate the "userdef" ThmSet of the current theory with K entries
   to simulate ml_progLib's situation (where ml_translator_testScript has
   already filled userdef/TypeBase/compute via Hol_defn/Datatype/etc.
   before our hot loop).  Raw Definition.new_definition alone does NOT
   register userdef entries, so without this the synthetic doesn't
   exercise the quadratic revise_data scan. *)
val K_prepop = 500
val _ = print ("  pre-populating userdef with " ^ Int.toString K_prepop
               ^ " entries...\n")
val _ = List.tabulate (K_prepop, fn i =>
  let val nm  = "pre_" ^ Int.toString i
      val lhs = mk_var (nm, bool)
      val def = Definition.new_definition (nm ^ "_def", mk_eq (lhs, T))
      val _   = DefnBase.register_defn {tag = "user", thmname = nm ^ "_def"}
  in () end)

(* Wrap TheoryDelta.NewConstant listeners with per-name timers. *)
val prof_hooks : (string, real ref) Redblackmap.dict ref =
    ref (Redblackmap.mkDict String.compare)
val enable_timing = ref false

local
  fun wrap_listener (name, f) =
      let val bucket = ref 0.0
          val _ = prof_hooks :=
                    Redblackmap.insert (!prof_hooks, name, bucket)
          fun timed ev =
              if !enable_timing then
                let val t0 = Time.now ()
                    val r = f ev
                    val t1 = Time.now ()
                    val _ = bucket := !bucket + Time.toReal (Time.- (t1, t0))
                in r end
              else f ev
      in (name, timed) end
  val existing = Listener.listeners Theory.delta_hook
  val _ = List.app
            (fn (s, _) => ignore (Listener.remove_listener Theory.delta_hook s))
            existing
  val _ = List.app
            (fn nf => Listener.add_listener Theory.delta_hook (wrap_listener nf))
            (List.rev existing)
in end

(* Split timers so we see mk_rhs vs the kernel call. *)
val t_rhs_ref = ref 0.0
val t_def_ref = ref 0.0

fun bench_one i =
  let val nm   = mk_name i
      val lhs  = mk_var (nm, bool)
      val tr0  = Time.now ()
      val rhs  = mk_rhs i
      val eq   = mk_eq (lhs, rhs)
      val tr1  = Time.now ()
      val _    = t_rhs_ref := !t_rhs_ref + Time.toReal (Time.- (tr1, tr0))
      val td0  = Time.now ()
      val _    = enable_timing := true
      val th   = Definition.new_definition (nm ^ "_def", eq)
      val _    = enable_timing := false
      val td1  = Time.now ()
      val _    = t_def_ref := !t_def_ref + Time.toReal (Time.- (td1, td0))
      (* cache the new constant (LHS of the returned definitional thm)
         to avoid O(sig) prim_mk_const lookups in subsequent mk_rhs. *)
      val (lhs_const, _) = dest_eq (concl th)
      val _    = Array.update (const_arr, i, lhs_const)
  in th end

val t_total0 = Time.now ()
val _ = List.tabulate (N, bench_one)
val t_total1 = Time.now ()

val dt_total = Time.toReal (Time.- (t_total1, t_total0))
val per_ms   = dt_total * 1000.0 / Real.fromInt N

val _ = print ("\n" ^ Int.toString N ^ " defs in "
               ^ Real.toString dt_total ^ " s"
               ^ " = " ^ Real.toString per_ms ^ " ms/call\n")
val _ = print ("    mk_rhs  (mk_conj + mk_eq): "
               ^ Real.toString (!t_rhs_ref) ^ " s\n")
val _ = print ("    new_definition call:       "
               ^ Real.toString (!t_def_ref) ^ " s\n")
val _ = print "  NewConstant listener breakdown:\n"
val _ = List.app
          (fn (nm, r) => print ("    " ^ nm ^ ":  "
                                ^ Real.toString (!r) ^ " s\n"))
          (Redblackmap.listItems (!prof_hooks))
val _ = print "\n"
