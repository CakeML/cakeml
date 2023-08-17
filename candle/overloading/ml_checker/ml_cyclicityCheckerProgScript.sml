(*
  An I/O shim for the verified cyclicity checker
*)
open preamble ml_translatorTheory ml_translatorLib ml_pmatchTheory patternMatchesTheory
open astTheory libTheory evaluateTheory semanticPrimitivesTheory
open ml_progLib ml_progTheory evaluateTheory
open set_sepTheory cfTheory cfStoreTheory cfTacticsLib Satisfy
open cfHeapsBaseTheory basisFunctionsLib
open ml_monadBaseTheory ml_monad_translatorTheory ml_monadStoreLib ml_monad_translatorLib
open holKernelTheory holKernelProofTheory
open basisProgTheory
open holAxiomsSyntaxTheory (* for setting up the context *)
open ml_hol_kernel_funsProgTheory ml_hol_kernelProgTheory (* for setting up the context *)
open fromSexpTheory
open astToSexprLib
open patternMatchesLib patternMatchesSyntax patternMatchesTheory

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

val _ = new_theory "ml_cyclicityCheckerProg";
val _ = translation_extends "ml_hol_kernelProg"

val () = ENABLE_PMATCH_CASES();

(* Can't do this with process_topdecs because the lexer doesn't support
   escape sequences for string literals.
 *)
Definition parse_strlit_innards_def:
  parse_strlit_innards cs acc =
  (case cs of
           (#"\"" ::cs) => SOME (REVERSE acc,cs)
         | (x::cs) =>
             parse_strlit_innards cs (x::acc)
         | [] => NONE)
End

val res = parse_strlit_innards_def |> translate_no_ind;

Triviality parse_strlit_innards_ind:
  parse_strlit_innards_ind
Proof
  rewrite_tac [fetch "-" "parse_strlit_innards_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (fetch "-" "parse_strlit_innards_ind")
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ fs [FORALL_PROD]
  \\ Cases_on ‘cs’ >> gvs[]
QED

val _ = parse_strlit_innards_ind |> update_precondition;

Definition parse_strlit_def:
  parse_strlit cs =
  (case cs of
    (#"\"" :: cs) => parse_strlit_innards cs []
   | _ => NONE)
End

val _ = Q.prove(
  ‘∀cs acc. parse_strlit_innards_side cs acc’,
  ho_match_mp_tac (fetch "-" "parse_strlit_innards_ind") >> rw[] >>
  REWRITE_TAC[Once $ fetch "-" "parse_strlit_innards_side_def"] >>
  Cases_on ‘cs’ >> gvs[]
  ) |> update_precondition

val _ = translate parse_strlit_def

val _ = (append_prog o process_topdecs) ‘
  fun parse_string cs =
    case parse_strlit cs of
      None => None
    | Some (str, cs) => Some (String.implode str, cs)
  ’

val _ = (append_prog o process_topdecs) ‘
  fun parse_skip_space l =
    case l of
      [] => []
    | (x::cs) =>
      if Char.isSpace x then
        parse_skip_space cs
      else (x::cs);
  ’

val _ = (append_prog o process_topdecs) ‘
  fun parse_token token cs =
    case cs of
      (c::cs) =>
        if c = token then
          Some cs
        else if Char.isSpace c then
          parse_token token cs
        else
          None
    | [] => None
  ’

val _ = (append_prog o process_topdecs) ‘
  fun parse_list_innards is_ordered parse_elem cs one_more_elem acc =
    case cs of
      c::cs =>
        if Char.isSpace c then
          parse_list_innards is_ordered parse_elem cs one_more_elem acc
        else if c = #"]" then
          if one_more_elem then
            None
          else (if is_ordered then
            Some(List.rev acc,cs)
          else
            Some(acc,cs))
        else
          (case parse_elem (c::cs) of
             None => None
           | Some (elem, cs) =>
               (case parse_token #";" cs of
                  None =>
                    (* end of list *)
                    (case parse_token #"]" cs of
                       None => None
                     | Some cs =>
                        if is_ordered then
                          Some(List.rev (elem::acc),cs)
                        else
                          Some(elem::acc,cs)
                    )
                | Some cs =>
                    parse_list_innards is_ordered parse_elem cs True (elem::acc)))
    | [] =>
        if one_more_elem then None
        else if is_ordered then
          Some(List.rev acc, [])
        else Some (acc, [])’

val _ = (append_prog o process_topdecs) ‘
  fun parse_list is_ordered parse_elem cs =
    case cs of
      c::cs =>
        if Char.isSpace c then
          parse_list is_ordered parse_elem cs
        else if c = #"[" then
          parse_list_innards is_ordered parse_elem cs False []
        else None
    | [] => None’

val _ = (append_prog o process_topdecs) ‘
  fun parse_type cs =
    case cs of
    (#"T" :: #"y" :: #"v" :: #"a" :: #"r" :: #" " :: cs) =>
      (case parse_string (parse_skip_space cs) of
         Some (name, cs) => Some (Kernel.Tyvar name, cs)
       | None => None)
  | (#"T" :: #"y" :: #"a" :: #"p" :: #"p" :: #" " :: cs) =>
      (case parse_string (parse_skip_space cs) of
         None => None
       | Some (name, cs) =>
           (case parse_list True parse_type cs of
              None => None
            | Some (tylist, cs) => Some (Kernel.Tyapp name tylist, cs)))
  | _ => None’

val _ = (append_prog o process_topdecs) ‘
  fun parse_pair parse_fst parse_snd cs =
    case parse_token #"(" cs of
      None => None
    | Some cs =>
      (case parse_fst (parse_skip_space cs) of
        None => None
      | Some (first, cs) =>
        (case parse_token #"," cs of
          None => None
        | Some cs =>
          (case parse_snd (parse_skip_space cs) of
            None => None
          | Some (second, cs) =>
            (case parse_token #")" cs of
              None => None
            | Some cs => Some ((first, second), cs)))))’

val _ = (append_prog o process_topdecs) ‘
  fun parse_sum parse_inl parse_inr cs =
    let val cs = parse_skip_space cs in
    case parse_inr cs of
      None =>
        (case parse_inl cs of
          None => None
        | Some (inl, cs) => Some (Inl inl, cs))
    | Some (inr, cs) => Some (Inr inr, cs)
    end’

val _ = (append_prog o process_topdecs)
  ‘fun parse_sum_hol_type x = parse_sum parse_type (parse_pair parse_string parse_type) x’

val _ = (append_prog o process_topdecs)
  ‘fun hol_type_sum_pairs x = parse_pair parse_sum_hol_type parse_sum_hol_type x’

val _ = (append_prog o process_topdecs) ‘
  fun intersperse_commas l =
      case l of [] => []
             | [e] => [e]
             | e::l => e:: "," :: intersperse_commas l’

val _ = (append_prog o process_topdecs) ‘
  fun present_type ty =
      case ty of (Kernel.Tyvar s) => "'" ^ s
              | (Kernel.Tyapp s []) => s
              | (Kernel.Tyapp s [t]) => present_type t ^ " " ^ s
              | (Kernel.Tyapp s l) =>
                  let
                    val ps = String.concat(intersperse_commas(List.map present_type l))
                  in
                    "(" ^ ps ^ ") " ^ s
                  end’

val _ = (append_prog o process_topdecs) ‘
  fun present_tot ty =
    case ty of (Inl ty) => present_type ty
            | (Inr(Kernel.Const name ty)) => name ^ " : " ^ present_type ty’

val _ = (append_prog o process_topdecs)
  ‘fun main u =
     let val cs = String.explode(TextIO.inputAll TextIO.stdIn);
     in
        (case parse_list False hol_type_sum_pairs cs of
          None => print "Parse error!\n"
        | Some(deps,_) =>
            (let
                val new_deps =
                    List.map(fn (x,y) =>
                              (case x of Inl x => Inl x
                                      | Inr(a,b) => Inr (Kernel.Const a b),
                               case y of Inl x => Inl x
                                       | Inr(a,b) => Inr(Kernel.Const a b))
                            ) deps ;
                val max_depth = 32767 ;
             in
               (case Kernel.dep_steps_compute new_deps max_depth new_deps of
                  Kernel.Maybe_cyclic =>
                    print "Cyclicity check timed out!\n"
                | Kernel.Cyclic_step (tot1,(tot2,tot3)) =>
                    (print "Found a cycle!\n";
                     print("  The path from " ^ present_tot tot1 ^ "\n");
                     print("  to " ^ present_tot tot2 ^ "\n");
                     print("  starts a cycle " ^ present_tot tot3 ^ "\n")
                    )
                | Kernel.Non_comp_step (p,(q,(p',_))) =>
                    (print "Dependency graph is non-composable!\n";
                     print("  The path from " ^ present_tot p ^ "\n");
                     print("  to " ^ present_tot q ^ "\n");
                     print("  does not compose with " ^ present_tot p' ^ "\n")
                    )
                | Kernel.Acyclic k =>
                    (print "SUCCESS: Dependency graph is acyclic!\n";
                     print("  Longest checked path: "
                            ^ (Int.toString (max_depth - k)) ^ "\n")
                    )
                )
             end
            ))
            handle Kernel.Fail s => print s
                 | _ => print "Unhandled exception raised!\n"
     end
  ’

val prog =
  “SNOC (Dlet unknown_loc (Pcon NONE []) (App Opapp [Var (Short "main"); Con NONE []]))
        ^(get_ml_prog_state() |> get_prog)
  ” |> EVAL |> concl |> rhs

val _ = astToSexprLib.write_ast_to_file "cyclicity_checker.sexp" prog;

val _ = export_theory();
