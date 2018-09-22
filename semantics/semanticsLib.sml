(*
  TODO: move
*)
structure semanticsLib :> semanticsLib =
struct

open preamble;
open semanticPrimitivesTheory;
open stringLib Boolconv ListConv1 pred_setLib;

val [ALL_DISTINCT_NIL,ALL_DISTINCT_CONS] = ALL_DISTINCT |> CONJUNCTS
val [MEM_NIL,MEM_CONS] = MEM |> CONJUNCTS
val [FLAT_NIL,FLAT_CONS] = FLAT |> CONJUNCTS
val [MAP_NIL,MAP_CONS] = MAP |> CONJUNCTS
val [APPEND_NIL_LEFT,APPEND_CONS] = APPEND |> CONJUNCTS
val APPEND_NIL_RIGHT = APPEND_NIL |> CONJUNCTS |> hd
val dec_case_def = fetch "ast" "dec_case_def" |> CONJUNCTS
val [set_nil,set_cons] = LIST_TO_SET |> CONJUNCTS

(* TODO: move to listLib, consolidate with IS_EL_CONV *)
fun mem_conv eq_conv tm =
  tm |> (
    REWR_CONV MEM_NIL
    ORELSEC
   (REWR_CONV MEM_CONS
     THENC RATOR_CONV(RAND_CONV(eq_conv))
     THENC OR_CONV
     THENC (fn tm => if Teq tm then ALL_CONV tm else mem_conv eq_conv tm))
   )

(* TODO: move to listLib, cf. Z3ProofReplay.ALL_DISTINCT_CONV *)
fun all_distinct_conv eq_conv tm =
  tm |> (
     REWR_CONV ALL_DISTINCT_NIL
     ORELSEC
     (REWR_CONV ALL_DISTINCT_CONS
      THENC RATOR_CONV(RAND_CONV(RAND_CONV(mem_conv eq_conv)))
      THENC RATOR_CONV(RAND_CONV(NOT_CONV))
      THENC AND_CONV
      THENC (fn tm => if Feq tm then ALL_CONV tm else all_distinct_conv eq_conv tm)
     )
  )

val all_distinct_string_conv = all_distinct_conv string_EQ_CONV
val all_distinct_list_string_conv = all_distinct_conv (list_EQ_CONV string_EQ_CONV)

fun set_conv tm =
  tm |>
  (
    REWR_CONV set_nil
    ORELSEC
    (REWR_CONV set_cons THENC RAND_CONV set_conv)
  )

end
