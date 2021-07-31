(*
  Parser for compactDSL programs
*)

open preamble
     timeLangTheory

val _ = new_theory "taParser";

Overload CVar = “strlit”;

local
  fun has_nat_prefix (#"%" :: #"n" :: #"a" :: #"t" :: _) = true
    | has_nat_prefix _ = false

  fun replace_nat_chars [] = []
    | replace_nat_chars xs =
        if has_nat_prefix xs
        then #"n" :: replace_nat_chars (List.drop(xs,4))
        else hd xs :: replace_nat_chars (tl xs)

  val replace_nat = implode o replace_nat_chars o explode
in
  fun parseFile fname filename =
    let
        val fd = TextIO.openIn filename
        val content = TextIO.inputAll fd handle e => (TextIO.closeIn fd; raise e)
        val _ = TextIO.closeIn fd
        val content = replace_nat content
    in
      Define [QUOTE (fname ^ " " ^ content)]
    end
end

val flashing_led_def =
      parseFile "flashing_led"
                "ta_progs/flashing_led.out";

val flashing_led_with_button_def =
      parseFile "flashing_led_with_button"
                "ta_progs/flashing_led_with_button.out";

val flashing_led_with_invariant_def =
      parseFile "flashing_led_with_invariant"
                "ta_progs/flashing_led_with_invariant.out";

val _ = export_theory();
