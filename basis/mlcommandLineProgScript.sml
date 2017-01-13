open preamble
     ml_translatorLib ml_progLib
     cfTheory cfHeapsTheory cfTacticsLib cfTacticsBaseLib basisFunctionsLib
     mlcharioProgTheory

val _ = new_theory "mlcommandLineProg";

val _ = translation_extends "mlcharioProg";
(*

val _ = ml_prog_update (open_module "mlcommandLine")
val e = ``(App Aw8alloc [Lit (IntLit 256); Lit (Word8 0w)])``

val _ = ml_prog_update (add_Dlet (derive_eval_thm "commandLine_state" e) "commandLine_state" [])

val commandLine_w8arrayToStrings = process_topdecs
  `fun w8arrayToStrings arr = 
    let
      fun f arr endStrings tempList i flag max =
        if (flag = 1) then
          endStrings
        else if (i = max) then
          endStrings
        else 
          if (CharIO.char_of_byte (Word8Array.sub (arr, i)) = #"\n") then
            f arr ((String.implode (List.rev tempList)) :: endStrings) [] (i + 1) 1 max
          else 
            f arr endStrings (CharIO.char_of_byte (Word8Array.sub (arr, i)) :: tempList) (i + 1) 0 max
    in f arr [] [] 0 0 (Word8Array.length arr) end`

val e =
  ``Let NONE (App (FFI "getArgs") [Var (Short "commandLine_state")])
      (LetApps "ss" ((*commandLine_w8arrayToStrings*) [Var (Short "commandLine_state")]
        (Apps [Var (Long "List" "hd"); Var (Short "ss")]))``
  |> EVAL |> concl |> rand

val _ = ml_prog_update(add_Dlet_Fun ``"name"`` ``"u`` e "name_v")

val e =
  ``Let NONE (App (FFI "getArgs") [Var (Short "commandLine_state")])
      (LetApps "ss" ((*commandLine_w8arrayToStrings*) [Var (Short "commandLine_state")]
        (Apps [Var (Long "List" "tl"); Var (Short "ss")]))``
  |> EVAL |> concl |> rand

val _ = ml_prog_update(add_Dlet_Fun ``"arguments"`` ``"u`` e "arguments_v")

val _ = ml_prog_update (close_module NONE);


val commandLine_fun_def = Define `
  commandLine_fun = (\i bytes s. case (bytes,s) of
      | (b, Str commandLine) ==>
        if i = "getArgs" then
          if (LENGTH b = 256) then
            if (LENGTH commandLine < 257) then 
              SOME ((MAP ORD commandLine ++ DROP (LENGTH commandLine) bytes), Str commandLine)
            else
              SOME ((MAP ORD (TAKE 256 commandLine)), Str commandLine)
          else NONE
        else NONE 
      | _ => NONE)` 


val COMMANDLINE_def = Define `
  COMMANDLINE (cl:string list) =
    IO (List (MAP Str cl)) commandline_fun ["get_args"]`


(*AIM: to be able to define echo using the arguments function so that
  `!cl. (*some specification about length of cl being less than 256*) ==>
  app (p:'ffi ffi_proj) echo_v [uv] (COMMANDLINE cl * STDOUT out)
  (POSTv u. COMMANDLINE cl * STDOUT (out ++ (CONCAT (MAP implode (arguments cl)))))`

  is true *)
*)
val _ = export_theory()

