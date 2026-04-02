
Theory rev_array
Ancestors
  itreeTau panLang panSem
  pan_itreeSem pan_itreeProps
  panItreeAbsSem
  panPtreeConversion
  alignment wordLang ffi misc
Libs
  preamble stringSyntax numSyntax
  stringLib sumSyntax
  HolKernel boolLib bossLib
  listSyntax mlstringLib optionSyntax
  simpLib panItreeDecompilerLib



val _ = set_trace "notify type variable guesses" 0;


(* Extension of itreeTauTheory *)
val _ = monadsyntax.enable_monadsyntax();
val _ = declare_monad("itree", {unit = “Ret”, bind = “itree_bind”,
                      ignorebind = NONE,
                      choice = NONE,
                      fail = NONE,
                      guard = NONE});
val _ = enable_monad "itree";

(* Unicode operator overloads *)
val _ = temp_set_fixity "≈" (Infixl 500);
Overload "≈" = “itree_wbisim”;
val _ = temp_set_fixity ">>=" (Infixl 500);
Overload ">>=" = “itree_bind”;

Overload "case" = “itree_CASE”;


                                                   
fun read_file fname = let
    val s = TextIO.openIn fname
    fun get ss = case TextIO.inputLine s of
        SOME str => get (str :: ss)
      | NONE => rev ss
  in concat (get []) end


(** Copied from panPtreeConversion *)
fun parse_pancake_code word_ty str =
  let
    val parse_topdecs_to_ast_s = inst [alpha |-> word_ty] “parse_topdecs_to_ast”
    val thm = EVAL (mk_comb (parse_topdecs_to_ast_s, stringLib.fromMLstring str))
    val r = rhs (concl thm)
  in
    if sumSyntax.is_inl r
    then (fst (sumSyntax.dest_inl r), thm)
    else failwith ("parse_pancake_code: failed to EVAL")
  end


fun parse_pancake_file word_ty fname =
  parse_pancake_code word_ty (read_file fname)

                     

val (rev_array_topdecs, _) = parse_pancake_file “:32” "rev_array.pnk"

val rev_array_fundecs = topdecs_to_fundecs rev_array_topdecs

val rev_array_result = decompile_2_reduce "rev_array" [] rev_array_fundecs


val rev_array_shallow = List.nth (fst rev_array_result, 0) |> (fn (x,y,z) => x)
                                           

Theorem itree_bind_resp_wbisim_compose_intro:
  t ≈ t' ⇒ (∀r. k r ≈ k' r) ⇒ t'' = t' >>= k' ⇒ t >>= k ≈ t''
Proof
  rw[]
  \\ irule itree_bind_resp_wbisim
  \\ gvs[]
QED
