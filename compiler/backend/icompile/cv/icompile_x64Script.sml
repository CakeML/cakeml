(*
  benchmarking stuff
  *)
open preamble
     eval_cake_icompile_x64Lib
     x64_configTheory
     eval_cake_compile_x64Lib;

val _ = Globals.max_print_depth := 10;
open catProgTheory
     diffProgTheory
     echoProgTheory
     grepProgTheory
     helloProgTheory
     helloErrProgTheory
     patchProgTheory
     sortProgTheory;


val _ = new_theory"icompile_x64";

val _ = Globals.max_print_depth := 10;

fun split_basis prog_name =
  let
    val prog_const = mk_const (prog_name, “: ast$dec list”);
    val basis = EVAL “TAKE 93 ^prog_const” |> rconc;
    val prog1 = EVAL “DROP 93 ^prog_const” |> rconc;
  in
    (basis, prog1)
  end;
(* set up config *)


val progs = [("cat_prog", cat_prog_def),
             ("diff_prog", diff_prog_def),
             ("echo_prog", echo_prog_def),
             ("grep_prog", grep_prog_def),
             ("hello_prog", hello_prog_def),
             ("helloErr_prog", helloErr_prog_def),
             ("patch_prog", patch_prog_def),
             ("sort_prog", sort_prog_def)];


Definition x64_config'_def:
  x64_config' =
  let conf = x64_backend_config in
  let source_conf' = conf.source_conf with <| do_elim := F; init_vidx := 100000 |> in
  let stack_conf' = conf.stack_conf with do_rawcall := F in
    conf with <| source_conf := source_conf';
                 stack_conf := stack_conf'|>
End

Definition x64_config''_def:
  x64_config'' =
  let conf = x64_backend_config in
  let source_conf' = conf.source_conf with <| do_elim := F; init_vidx := 100000 |> in
    conf with <| source_conf := source_conf' |>
End

val x64_conf_default_def = CONV_RULE (RAND_CONV EVAL) x64_config''_def; (* yes optimisation *)
val x64_conf_alt_def = CONV_RULE (RAND_CONV EVAL) x64_config'_def;      (* no optimisation *)
val x64_inc_conf_default_tm = backendTheory.config_to_inc_config_def
                                 |> ISPEC (x64_conf_default_def |> rconc)
                                 |> CONV_RULE (RAND_CONV EVAL) |> rconc;
val x64_inc_conf_alt_tm = backendTheory.config_to_inc_config_def
                         |> ISPEC (x64_conf_alt_def |> rconc)
                         |> CONV_RULE (RAND_CONV EVAL) |> rconc;

(* example usage *)
(*
val (basis_prog_tm, hello_prog1_tm) = split_basis "hello_prog";

val (init_icomp_thm, init_icomp_empty, init_ic_name) = init_icompile x64_inc_conf;

val (basis_prog_icomp, basis_prog_ic_name) = icompile init_ic_name init_icomp_empty "basis_prog" basis_prog_tm;

val (hello_prog1_icomp, hello_prog_ic_name) = icompile basis_prog_ic_name basis_prog_icomp "hello_prog1" hello_prog1_tm;

val final_thm = end_icompile init_icomp_thm
                             hello_prog1_icomp
                             hello_prog_ic_name
                             x64_inc_conf;

print_to_file final_thm "hello_prog_ic_with_lib.S";

eval_cake_compile_x64_with_conf "" x64_conf_def hello_prog_def  "hello_monocomp.S" ;
*)




local
   val second = Time.fromReal 1.0
   val minute = Time.fromReal 60.0
   val year0 = Date.year (Date.fromTimeUniv Time.zeroTime)
   fun to_str i u = if i = 0 then "" else Int.toString i ^ u
in
   fun time_to_string t =
      if Time.< (t, second)
         then Time.fmt 5 t ^ "s"
      else if Time.< (t, minute)
         then Time.fmt 1 t ^ "s"
      else let
              val d = Date.fromTimeUniv t
              val years = Date.year d - year0
              val days = Date.yearDay d
              val hours = Date.hour d
              val minutes = Date.minute d
           in
              if years + days + hours = 0 andalso minutes < 10 then
                 to_str minutes "m" ^ Date.fmt "%Ss" d
              else to_str years "y" ^ to_str days "d" ^ to_str hours "h" ^
                   Date.fmt "%Mm%Ss" d
           end
end



fun start_time () = Timer.startCPUTimer ();

fun end_time timer =
   let
      val {sys, usr} = Timer.checkCPUTimer timer
      val gc = Timer.checkGCTime timer
   in

       (usr,
        gc,
        sys)
   end

fun time1 f x =
   let
      val timer = start_time ()
      val y = f x handle e => (end_time timer; raise e)
   in
      (end_time timer, y)
   end

fun time2 f x1 x2 =
   let
      val timer = start_time ()
      val y = f x1 x2 handle e => (end_time timer; raise e)
   in
      (end_time timer, y)
   end

fun time3 f x1 x2 x3 =
   let
      val timer = start_time ()
      val y = f x1 x2 x3 handle e => (end_time timer; raise e)
   in
      (end_time timer, y)
   end

fun time4 f x1 x2 x3 x4 =
   let
      val timer = start_time ()
      val y = f x1 x2 x3 x4 handle e => (end_time timer; raise e)
   in
      (end_time timer, y)
   end


fun run_icompile_whole prog_name x64_inc_conf =
  let
    val (basis_prog_tm, prog1_tm) = split_basis prog_name;
    val (init_icomp_thm, init_icomp_empty, init_ic_name) = init_icompile x64_inc_conf;
    val (basis_prog_icomp, basis_prog_ic_name) = icompile init_ic_name init_icomp_empty "basis_prog" basis_prog_tm;
    val (prog1_icomp, prog1_ic_name) = icompile basis_prog_ic_name basis_prog_icomp (prog_name^"1") prog1_tm;
    val final_thm = end_icompile init_icomp_thm
                                 prog1_icomp
                                 prog1_ic_name
                                 x64_inc_conf;
    val _ = print_to_file final_thm (prog_name^"_icompiled.S");
    in () end;

fun rq1 progs =
  let
    fun loop progs acc =
      case progs of
        [] => acc
      | ((pname, pdef) :: progs') =>
          let
            val desc = "results for " ^ pname;
            val (duration_for_c, res_for_c) =
              time4 eval_cake_compile_x64_with_conf "" x64_conf_alt_def pdef  "diff_mcomp.S" ;
            val (duration_for_ic, res_for_ic) =
              time2 run_icompile_whole pname x64_inc_conf_alt_tm;
            val row = (desc, duration_for_c, duration_for_ic);
          in
            loop progs' (row :: acc)
          end;
    val table = loop progs [];
  in
    table
  end;

fun addt3 (t1, t2, t3) (t1', t2', t3') : Time.time * Time.time * Time.time =
                                         (t1 + t1', t2 + t2', t3 + t3');

fun format_t3 (t1, t2, t3) =
   ("user: "^ time_to_string t1, "gc: " ^ time_to_string t2, "sys: " ^ time_to_string t3);


fun rq2or3 progs conf_for_c =
  let
    val name_of_fst_prog = hd progs |> fst;
    val (basis_prog_tm, _ ) = split_basis name_of_fst_prog;
    val progs_w_tm = map (fn (pname, pdef) =>
                         let
                           val prog1tm = split_basis pname |> snd;
                         in
                           (pname, prog1tm, pdef)
                           end) progs;
    val _ = PolyML.fullGC();
    val sum_time = foldl
                   (fn (curr, acc) =>
                      let
                        val (pname, pdef) = curr;
                        val ((runt, gct, syst), r) = time4 eval_cake_compile_x64_with_conf "" conf_for_c pdef (pname ^ "_mcomp_rq2.S");
                        val (prev_runt, prev_gct, prev_syst) = acc;
                        val acc' = (runt + prev_runt, gct + prev_gct, syst + prev_syst);
                      in
                        acc'
                      end) (Time.zeroTime, Time.zeroTime, Time.zeroTime) progs;
    val _ = PolyML.fullGC();
    val (init_duration, (init_icomp_thm, init_icomp_empty, init_ic_name)) = time1 init_icompile x64_inc_conf_alt_tm;
    val (basis_duration, (basis_prog_icomp, basis_prog_ic_name)) = time4 icompile init_ic_name init_icomp_empty "basis_prog" basis_prog_tm;
    val sum_time_ic = foldl
                      (fn (curr, acc) =>
                         let
                           val (pname, ptm, pdef) = curr;
                           val (prog_ic_duration, (prog1_icomp, prog1_ic_name)) = time4 icompile basis_prog_ic_name basis_prog_icomp (pname^"1") ptm;
                           val (end_ic_duration, final_th) = time4 end_icompile init_icomp_thm
                                                                               prog1_icomp
                                                                               prog1_ic_name
                                                                               x64_inc_conf_alt_tm;

                           val (print_duration, ()) = time2 print_to_file final_th (pname^"_icompiled_rq2.S");
                         in
                           acc |> addt3 prog_ic_duration |> addt3 end_ic_duration |> addt3 print_duration end)

                      (Time.zeroTime, Time.zeroTime, Time.zeroTime)
                      progs_w_tm;
  in
    (sum_time |> format_t3, init_duration |> addt3 basis_duration |> addt3 sum_time_ic |> format_t3)
    end;

    
(* returns res where
   fst res : the total time taken to run the compiler on all the programs without optimisations
   snd res : the total time taken to run the icompiler on all the programs without optimisations
             with basis compiled incrementally *)

val resrq2 = rq2or3 progs x64_conf_alt_def;



(* returns res where
   fst res : the total time taken to run the compiler on all the programs WITH  optimisations
   snd res : the total time taken to run the icompiler on all the programs without optimisations
             with basis compiled incrementally *)
val resrq3 = rq2or3 progs x64_backend_config_def;


val _ = export_theory();
