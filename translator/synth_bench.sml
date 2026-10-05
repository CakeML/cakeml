(* Synthetic benchmark for tree-backed nsLookup infrastructure.
   Does N sorted writes and M lookups. Compare wall time and the
   per-phase profile to see pure throughput, isolated from
   translator proof work. *)

load "ml_progLib";
open ml_progLib ml_progTheory HolKernel boolLib bossLib Parse;

val N = 500    (* number of writes *)
val M = 200    (* number of lookups *)

fun pad n =
    let val s = Int.toString n
        val pad = "0000" ^ s
    in String.extract (pad, String.size pad - 4, NONE) end

fun write_iter i env_name =
    let val key = "k" ^ pad i
        val prev_const = mk_var (env_name, mk_type ("sem_env",
                           [mk_type ("v", [])]))
        val next_name = "s" ^ Int.toString i
        val def_tm =
            Parse.Term [QUOTE (next_name ^ " = write (strlit \"" ^ key ^
                               "\") (Litv (IntLit " ^ Int.toString i ^
                               ")) " ^ env_name)]
        val def = Definition.new_definition (next_name ^ "_def", def_tm)
    in (next_name, def) end

val _ = print ("\n=== synthetic bench: " ^ Int.toString N ^
               " writes, " ^ Int.toString M ^ " lookups ===\n")

val write_start = Time.now ()

val final_name =
    let fun loop i prev_name =
            if i >= N then prev_name
            else let val (next_name, def) = write_iter i prev_name
                     val _ = ignore (derive_nsLookup_tree def)
                 in loop (i+1) next_name end
    in loop 0 "init_env" end

val write_elapsed =
    Time.toReal (Time.- (Time.now (), write_start))
val _ = print ("writes done in " ^ Real.toString write_elapsed ^ " s\n")

(* Lookups - scattered keys. *)
val lookup_start = Time.now ()

val final_env_var = mk_var (final_name, mk_type ("sem_env",
                      [mk_type ("v", [])]))
val v_accessor = prim_mk_const
    {Name = "recordtype.sem_env.seldef.v", Thy = "semanticPrimitives"}
val env_v_tm = mk_icomb (v_accessor, final_env_var)
val nsLookup_Short_tm = prim_mk_const
    {Name = "nsLookup_Short", Thy = "ml_prog"}

fun do_lookup i =
    let val key_str = "k" ^ pad (i * (N div M))
        val key_tm = mlstringSyntax.mk_mlstring key_str
        val tm = list_mk_comb (nsLookup_Short_tm, [env_v_tm, key_tm])
    in nsLookup_conv tm end

val _ = List.tabulate (M, do_lookup)

val lookup_elapsed =
    Time.toReal (Time.- (Time.now (), lookup_start))
val _ = print ("lookups done in " ^ Real.toString lookup_elapsed ^ " s\n")

val _ = ml_progLib.print_let_env_profile ()
