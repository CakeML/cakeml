(*
  Mechanism for adding runtime type checking annotations, used in the Candle
  prover soundness proofs.
 *)

structure runtime_checkLib :> runtime_checkLib = struct

open HolKernel boolLib bossLib BasicProvers mlstringTheory runtime_checkTheory;

fun mlstring_check s =
  “mlstring$strlen ^s”;

fun type_check ty =
  “case ^ty of Tyvar _ => () | _ => abc” |> subst [“abc:unit”|->“()”];

fun term_check tm =
  “case ^tm of Const _ _ => () | _ => abc” |> subst [“abc:unit”|->“()”];

fun thm_check th =
  “case ^th of Sequent _ _ => ()”;

fun ty_list_check ty = “check_ty ^ty”;
fun tm_list_check tm = “check_tm ^tm”;
fun thm_list_check th = “check_thm ^th”;
fun ty_ty_list_check tyty = “check_ty_ty ^tyty”;
fun tm_tm_list_check tmtm = “check_tm_tm ^tmtm”;

fun guess_check tm =
  if type_of tm = “:mlstring” then mlstring_check else
  if type_of tm = “:type” then type_check else
  if type_of tm = “:term” then term_check else
  if type_of tm = “:thm” then thm_check else
  if type_of tm = “:type list” then ty_list_check else
  if type_of tm = “:term list” then tm_list_check else
  if type_of tm = “:thm list” then thm_list_check else
  if type_of tm = “:(type # type) list” then ty_ty_list_check else
  if type_of tm = “:(term # term) list” then tm_tm_list_check else fail()

fun add_type_check v f def = let
  val def = SPEC_ALL def
  val tm = f v
  in MATCH_MP pure_seq_intro def |> ISPEC tm end

fun check [] def = SPEC_ALL def
  | check (v::vs) def =
    let
      val def = check vs def
      val tm = Parse.parse_in_context (free_vars (concl def)) v
      val f = guess_check tm
      val def = add_type_check tm f def
    in def end


end

