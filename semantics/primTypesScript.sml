(*
  Definition of the primitive types that are in scope before any CakeML program
  starts. Some of them are generated by running an initial program.
*)

open HolKernel Parse boolLib bossLib;
open semanticPrimitivesTheory evaluateTheory typeSystemTheory;

val _ = new_theory "primTypes"

(* The ordering in the following is important. The stamps generated from the
   exceptions and types must match those in semanticPrimitives *)
Definition prim_types_program_def:
  prim_types_program =
   [Dexn unknown_loc "Bind" [];
    Dexn unknown_loc "Chr" [];
    Dexn unknown_loc "Div" [];
    Dexn unknown_loc "Subscript" [];
    Dtype unknown_loc [([],"bool",[("False",[]); ("True",[])])];
    Dtype unknown_loc
          [(["'a"],"list",
            [("[]",[]); ("::",[Atvar "'a"; Atapp [Atvar "'a"] (Short "list")])])]]
End

Definition add_to_sem_env_def:
  add_to_sem_env (st:'ffi state,env) prog =
  case evaluate_decs st env prog of
    (st,Rval env') => SOME (st,extend_dec_env env' env)
  | (st,Rerr _) => NONE
End

Definition prim_sem_env_def:
  prim_sem_env (ffi:'ffi ffi_state) =
  add_to_sem_env
  (<|clock := 0; ffi := ffi; refs := []; next_type_stamp := 0;
     next_exn_stamp := 0; eval_state := NONE;
     fp_state := <|
       rws := [];
       opts := (λ x. []);
       choices := 0;
       canOpt := Strict;
       real_sem := F;
     |>
   |>,
   <|v := nsEmpty; c := nsEmpty|>) prim_types_program
End

Definition prim_tenv_def:
  prim_tenv =
     <|c :=
         alist_to_ns
           (REVERSE
              [("Bind",[],[],Texn_num); ("Chr",[],[],Texn_num);
               ("Div",[],[],Texn_num); ("Subscript",[],[],Texn_num);
               ("False",[],[],Tbool_num); ("True",[],[],Tbool_num);
               ("[]",["'a"],[],Tlist_num);
               ("::",["'a"],[Tvar "'a"; Tlist (Tvar "'a")],Tlist_num)]);
       v := nsEmpty;
       t :=
         alist_to_ns
           (REVERSE
              [("array",["'a"],Tapp [Tvar "'a"] Tarray_num);
               ("bool",[],Tapp [] Tbool_num);
               ("char",[],Tapp [] Tchar_num);
               ("double",[],Tapp [] Tdouble_num);
               ("exn",[],Tapp [] Texn_num);
               ("int",[],Tapp [] Tint_num);
               (* Tfn is ->, specially handled *)
               ("list",["'a"],Tapp [Tvar "'a"] Tlist_num);
               ("ref",["'a"],Tapp [Tvar "'a"] Tref_num);
               ("string",[],Tapp [] Tstring_num);
               ("unit",[],Tapp [] Ttup_num);
               (* pairs are specially handled *)
               ("vector",["'a"],Tapp [Tvar "'a"] Tvector_num);
               ("word64",[],Tapp [] Tword64_num);
               ("word8",[],Tapp [] Tword8_num);
               ("word8array",[],Tapp [] Tword8array_num)])|>
End

Definition prim_type_ids_def:
  prim_type_ids = set (Tlist_num::Tbool_num::prim_type_nums)
End

val _ = export_theory()
