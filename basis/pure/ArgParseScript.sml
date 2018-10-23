(*
  Pure functions for parsing of command-line arguments.
*)
open preamble mlstringTheory
open pegTheory pegexecTheory pegLib

val _ = new_theory"ArgParse";

(* Datatype representing each posible argument/flag/option in a
   tipical command line argument list (eg: char* argv[] in C)
*)
val _ = Datatype`
  arg =
  (* Simple flags of the form -<ident> eg: -h *)
         ShortFlag mlstring
  (* Long flags of the form --<ident>+ eg: --help *)
       | LongFlag mlstring
  (* Long flags with option of the form --<ident>+=<ident>+
     eg: --arch=arm6 *)
       | OptionFlag mlstring mlstring
  (* Standalone option of the form <ident>+ eg: cake.S*)
       | Option mlstring
  (* Where <ident> is equal to the regular expression [a-zA-Z0-9.-/_]
     (or similar) *)
`;

(* An arbitrary term of 'arg' to serve as ARB in some definitions *)
val arb_arg_def = Define`
  arb_arg = Option (implode "")
`;

(* Destructors for 'arg' terms *)

val destShortFlag_def = Define`
  destShortFlag (ShortFlag flag) = flag ∧
  destShortFlag _ = (implode "")
`;

val destOption_def = Define`
  destOption (Option opt) = opt ∧
  destOption _ = (implode "")
`;

val destLongFlag_def = Define`
  destLongFlag (LongFlag flag) = flag ∧
  destLongFlag _ = (implode "")
`;

val destOptionFlag_def = Define`
  destOptionFlag (OptionFlag flag opt) = (flag,opt) ∧
  destOptionFlag _ = ((implode ""),(implode ""))
`;

(* Auxiliary functions *)

(* Get the name of each flag and the empty string in case of an option *)
val getFlagName_def = Define`
  getFlagName (ShortFlag f)    = f   ∧
  getFlagName (LongFlag f)     = f   ∧
  getFlagName (OptionFlag f _) = f ∧
  getFlagName _                = implode ""
`;

(* Wheter the argument is a Flag *)
val isFlag_def = Define`
  isFlag (Option _) = F ∧
  isFlag _          = T
`;

(* Pretty prints values or type 'arg' *)
val showFlag_def = Define`
  showFlag (ShortFlag f)     = implode "-"  ^ f ∧
  showFlag (LongFlag f)      = implode "--" ^ f ∧
  showFlag (OptionFlag f s)  = implode "--" ^ f ^ implode "=" ^ s ∧
  showFlag (Option s)        = s
`;

(* Expands shortFlag(s) into single values when grouped in a single
   shortFlag (eg: '[ShortFlag "ab"]' expands to [ShortFlag "a", ShortFlag "b"])
 *)

val expandArgs_def = Define`
  expandArgs l =
    let expandFlags = MAP (ShortFlag o str) o explode;
        expand = λx l.
          case x of ShortFlag x => expandFlags x ++ l
                  | _           => x :: l
    in FOLDR expand [] l
`;

(* Flags description types *)
val _ = Datatype`
  flagConf = <| name       : mlstring; (* Long flag  ("-"  if disable) *)
                short      : char;     (* Short flag (#"-" if disable) *)
                desc       : mlstring; (* Short description used in the help msg *)
                has_option : bool;     (* Does it have and acompaning option/value? *)
                (* Continuation modifing the underlying structure
                   representing the options where 'flag.cont opt x' takes
                   an optional value 'opt' and a value 'x' of ''a' and
                   uses these to update 'x' to represent the precense of
                   the flag 'flag.name' or 'flag.short' with potentially
                   some argument
                 *)
                cont : mlstring option -> 'a -> 'a |>
`;


val matchArgs_def = Define`
  matchArg [] arg mOpt a = (if isFlag arg
                            then INL (implode "Unrecognized flag: " ^ showFlag arg)
                            (* TODO: Check for extra options *)
                            else INR (a,F)) ∧
  matchArg (f::fs) arg mOpt a =
    let flagName = getFlagName arg;
        strEq = (λx y. case compare x y of Equal => T | _ => F);
        pArg = showFlag arg;
        (* Does the current argument match with the current flag options? *)
        matchFlag  = (isFlag arg ∧ (* is the current argument a flag? *)
                     (strEq f.name flagName ∨  (* match the long name?  *)
                      strEq (str f.short) flagName)) (* match the short name? *)
    in if matchFlag
       then if f.has_option
            then case arg of
                     OptionFlag _ opt => INR (f.cont (SOME opt) a,F)
                  | _ => if IS_SOME mOpt
                         then INR (f.cont mOpt a,T)
                         else INL (implode "Missing value to: " ^ pArg)
            else case arg of
                     OptionFlag _ _ => INL (implode "Malformed flag: " ^ pArg)
                  | _               => INR (f.cont NONE a,F)
       else matchArg fs arg mOpt a
`;

(* Given a configuration (`:flag list`), an initial representing value,
   and a list of parsed arguments `:arg list`, `mkArgsConf confs init args`
   folds `args` over `init` using the apropiate continuation from
   matching flags/options
*)
val mkArgsConf_def = tDefine "mkArgsConf" `
  mkArgsConf fs a [] = INR a ∧
  mkArgsConf fs a (x::xs) =
    let flagOpt = (* Tries to find and option after a flag *)
          case xs of (* Look for the tail of the argument list *)
              []      => NONE (* If empty there is no extra option *)
            | (x::xs) => if isFlag x (* is the next value a flag? *)
                         then NONE   (* There is no option then *)
                         else SOME (destOption x) (* That is your option *)
    in
    case matchArg fs x flagOpt a of
        INL m => INL m
     |  INR (b,T) => mkArgsConf fs b (DROP 1 xs)
     |  INR (b,F) => mkArgsConf fs b xs`
(wf_rel_tac `measure (LENGTH o SND o SND)` >> rw [LENGTH]);

(* PEG grammar *)

(* Non Terminal for the grammar *)
val _ = Datatype`
  arg_NT = init_NT
         | ShortFlag_NT
         | LongFlag_NT
         | OptionFlag_NT
         | Option_NT
`;

(* Some abbreviations to make things nicer *)
val _ = type_abbrev("NT", ``:arg_NT inf``);
val _ = overload_on("mkNT", ``INL : arg_NT -> NT``);


(* Generates a 'pegsym' non terminal from a 'arg_NT' *)
(* TODO: maybe generalize this? *)
val pnt_def = Define`pnt ntsym = nt (mkNT ntsym) I`;

(* have to use these versions of choicel and pegf below because the
   versions from pegTheory use ARB in their definitions.
   Logically, the ARBs are harmless, but they completely mess with the
   CakeML translator.
*)

(* Chooses from a list of posible options *)
val choicel_def = Define`
  choicel [] = not (empty arb_arg) arb_arg ∧
  choicel (h::t) = choice h (choicel t) (λs. case s of INL x => x | INR y => y)
`;

(* Applies a function over the result of 'sym' *)
val pegf_def = Define`pegf sym f = seq sym (empty arb_arg) (λl1 l2. f l1)`;

(* Some proofs about pegf and choicel *)

val peg_eval_choicel_NIL = store_thm(
  "peg_eval_choicel_NIL[simp]",
  ``peg_eval G (i0, choicel []) x = (x = NONE)``,
  simp[choicel_def, Once peg_eval_cases]);

val peg_eval_choicel_CONS = store_thm(
  "peg_eval_choicel_CONS",
  ``∀x. peg_eval G (i0, choicel (h::t)) x ⇔
          peg_eval G (i0, h) x ∧ x <> NONE ∨
          peg_eval G (i0,h) NONE ∧ peg_eval G (i0, choicel t) x``,
  simp[choicel_def, SimpLHS, Once peg_eval_cases] >>
  simp[pairTheory.FORALL_PROD, optionTheory.FORALL_OPTION]);

val peg0_choicel = store_thm(
  "peg0_choicel[simp]",
  ``(peg0 G (choicel []) = F) ∧
    (peg0 G (choicel (h::t)) ⇔ peg0 G h ∨ pegfail G h ∧ peg0 G (choicel t))``,
  simp[choicel_def])

val peg0_pegf = store_thm(
  "peg0_pegf[simp]",
  ``peg0 G (pegf s f) = peg0 G s``,
  simp[pegf_def])

val tokeq_def = Define`tokeq t f = tok ((=) t) (K (f t))`;

val grabWS_def = Define`
  grabWS s = rpt (tok isSpace (K arb_arg)) (K arb_arg) ~> s
`;

(* Identifiers *)
(* TODO: add extra characters [-._/\] *)
val ident_def = Define`
  ident = let isOkChar = (λc. isAlphaNum c ∨ MEM c "._\\/");
              id       = tok isOkChar (λt. Option (implode [FST t]));
              arb_str  = implode "";
              joins    = Option o FOLDR (λw l. strcat (destOption w) l) arb_str;
              join     = (λx y. Option (strcat (destOption x) (destOption y)))
          in seq id (rpt id joins) join

`;

val argPEG_def = zDefine`
  argPEG : (char, arg_NT, arg) peg = <|
    start := pnt init_NT ;
    rules :=
    FEMPTY |++
    (*  A argument is one of four options *)
    [(mkNT init_NT, choicel [pnt ShortFlag_NT;
                             pnt LongFlag_NT;
                             pnt OptionFlag_NT;
                             pnt Option_NT]);
     (* A short flag, containing 1 or more letters, each letter
        representing a diferent flag
      *)
     (mkNT ShortFlag_NT, tokeq #"-" (K arb_arg) ~>
                               pegf ident (ShortFlag o destOption));
     (* A long flag *)
     (mkNT LongFlag_NT, (tokeq #"-" (K arb_arg) ~> tokeq #"-" (K arb_arg) ~>
                              pegf ident (LongFlag o destOption))
                         <~ not (tokeq #"=" (K arb_arg)) arb_arg);
     (* A Composed flag with an attached value *)
     (mkNT OptionFlag_NT, tokeq #"-" (K arb_arg) ~> tokeq #"-" (K arb_arg) ~>
                             seq ident                      (* Flag *)
                                 (tokeq #"=" (K arb_arg) ~> (* = *)
                                 ident)                     (* Value *)
                                 (λopt str. OptionFlag (destOption opt)
                                                       (destOption str)));
     (* Any other option *)
     (mkNT Option_NT, ident)
    ]|>
`;

(* wfG proof for argPEG *)
val argPEG_start = save_thm(
  "argPEG_start[simp]",
  SIMP_CONV(srw_ss())[argPEG_def]``argPEG.start``);

val ds = derive_compset_distincts ``:arg_NT``
val {lookups,fdom_thm,applieds} =
  derive_lookup_ths {pegth = argPEG_def
                    , ntty = ``:arg_NT``
                    , simp = SIMP_CONV (srw_ss())};

val argPEG_exec_thm = save_thm(
  "argPEG_exec_thm",
  LIST_CONJ(argPEG_start::ds::lookups));

val _ = computeLib.add_persistent_funs["argPEG_exec_thm"];
val _ = save_thm("FDOM_argPEG", fdom_thm);
val _ = save_thm("argPEG_applied", LIST_CONJ applieds);

val frange_image = prove(
  ``FRANGE fm = IMAGE (FAPPLY fm) (FDOM fm)``,
  simp[finite_mapTheory.FRANGE_DEF, pred_setTheory.EXTENSION] >> metis_tac[]);

val argPEG_range =
    SIMP_CONV (srw_ss())
              (fdom_thm :: frange_image :: applieds)
              ``FRANGE argPEG.rules``;

val subexprs_pnt = prove(
  ``subexprs (pnt n) = {pnt n}``,
  simp[subexprs_def, pnt_def]);

val Gexprs_argPEG = save_thm(
  "Gexprs_argPEG",
  ``Gexprs argPEG``
    |> SIMP_CONV (srw_ss())
         [Gexprs_def, subexprs_def,
          subexprs_pnt, argPEG_start, argPEG_range,
          ignoreR_def, ignoreL_def,
          choicel_def, tokeq_def, pegf_def, grabWS_def,
          checkAhead_def,
          pred_setTheory.INSERT_UNION_EQ
         ]);

val wfpeg_rwts = wfpeg_cases
                   |> ISPEC ``argPEG``
                   |> (fn th => map (fn t => Q.SPEC t th)
                                    [`seq e1 e2 f`, `choice e1 e2 f`, `tok P f`,
                                     `any f`, `empty v`, `not e v`, `rpt e f`,
                                     `tokeq t f`, `pegf e f`, `choicel []`,
                                     `choicel (h::l)`
                      ])
                   |> map (CONV_RULE
                             (RAND_CONV (SIMP_CONV (srw_ss())
                                [choicel_def, tokeq_def, ignoreL_def,
                                 ignoreR_def, pegf_def, grabWS_def])));

val peg0_grabWS = Q.prove(
  `peg0 argPEG (grabWS e) = peg0 argPEG e`,
  simp [ignoreL_def, grabWS_def, peg0_rules]);

val wfpeg_grabWS = (* wfpeg argPEG (grabWS e) ⇔ wfpeg argPEG e *)
  SIMP_CONV (srw_ss()) ([grabWS_def, ignoreL_def, peg0_grabWS] @ wfpeg_rwts)
                       ``wfpeg argPEG (grabWS e)``;

val wfpeg_pnt = wfpeg_cases
                  |> ISPEC ``argPEG``
                  |> Q.SPEC `pnt n`
                  |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [pnt_def]));


val peg0_rwts = peg0_cases
                  |> ISPEC ``argPEG`` |> CONJUNCTS
                  |> map (fn th => map (fn t => Q.SPEC t th)
                                       [`tok P f`, `choice e1 e2 f`, `seq e1 e2 f`,
                                        `tokeq t f`, `empty l`, `not e v`, `rpt e f`])
                  |> List.concat
                  |> map (CONV_RULE
                            (RAND_CONV (SIMP_CONV (srw_ss())
                                                  [tokeq_def])));

val pegfail_t = ``pegfail``;

val peg0_rwts = let
  fun filterthis th = let
    val c = concl th
    val (l,r) = dest_eq c
    val (f,_) = strip_comb l
  in
    not (same_const pegfail_t f) orelse is_const r
  end
in
  List.filter filterthis peg0_rwts
end;

val pegnt_case_ths = peg0_cases
                      |> ISPEC ``argPEG`` |> CONJUNCTS
                      |> map (Q.SPEC `pnt n`)
                      |> map (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [pnt_def])))

fun pegnt(t,acc) = let
  val th =
      prove(``¬peg0 argPEG (pnt ^t)``,
            simp (pegf_def::ident_def::fdom_thm::choicel_def::ignoreL_def::grabWS_def::ignoreR_def::applieds @ pegnt_case_ths) >>
            simp(peg0_rwts @ acc))
  val nm = "peg0_" ^ term_to_string t
  val th' = save_thm(nm, SIMP_RULE bool_ss [pnt_def] th)
  val _ = export_rewrites [nm]
in
  th::acc
end;

val npeg0_rwts =
    List.foldl pegnt []
   [``ShortFlag_NT``
   ,``LongFlag_NT``
   ,``OptionFlag_NT``
   ,``Option_NT``];

fun wfnt(t,acc) = let
  val th =
    prove(``wfpeg argPEG (pnt ^t)``,
          SIMP_TAC (srw_ss())
                   (applieds @
                    [wfpeg_pnt, fdom_thm, ignoreL_def, ignoreR_def,
                     checkAhead_def, ident_def]) THEN
          fs(peg0_grabWS :: wfpeg_grabWS :: wfpeg_rwts @ npeg0_rwts @ acc) THEN
         rw [choicel_def])
in
  th::acc
end;

val wfpeg_thm = LIST_CONJ (List.foldl wfnt [] [``ShortFlag_NT``
                                              ,``LongFlag_NT``
                                              ,``OptionFlag_NT``
                                              ,``Option_NT``
                                              ,``init_NT``]);

(* This is the actual well-formedness proof for argPEG *)
val wfG_argPEG = store_thm(
  "wfG_argPEG",
  ``wfG argPEG``,
  rw[wfG_def,Gexprs_argPEG,ident_def] >>
  srw_tac[boolSimps.DNF_ss][] >>
  simp(wfpeg_thm :: wfpeg_rwts));

(* Export 'wfG argPEG' into the simpset *)
val _ = export_rewrites ["wfG_argPEG"];

(* Setup monad syntax for the 'option' monad *)
val _ = monadsyntax.temp_add_monadsyntax()
val _ = overload_on ("monad_bind", “OPTION_BIND”)
val _ = overload_on ("assert", “OPTION_GUARD”)

val _ = computeLib.add_persistent_funs ["option.OPTION_BIND_def",
                                        "option.OPTION_IGNORE_BIND_def",
                                        "option.OPTION_GUARD_def",
                                        "option.OPTION_CHOICE_def"];


(* Default start location *)
(* TODO: make sure this is correct *)
val start_locs_def = Define`
  start_locs : locs = Locs (<|row := 0 ; col := 0 ; offset := 0|>)
                           (<|row := 0 ; col := 0 ; offset := 0|>)
`;

(* Given a 'string' generates a '(char, locs) alist' with information
   about the location of each character in the string
*)
val add_locs_def = Define`
  add_locs l =
    let new_char loc = loc with <| col  := loc.col + 1 ;
                                 offset := loc.offset + 1 |>;
        new_line loc = loc with <| row  := loc.row + 1 ;
                                 offset := loc.offset + 1 ;
                                 col    := 0 |>;
       update_locs locs f = locs_CASE locs (λl r. Locs (f l) (f r));
       update c (locs,s) = case c of
                            | #"\n" => let l = update_locs locs new_line
                                       in (l,(#"\n",l)::s)
                            | _     => let l = update_locs locs new_char
                                       in (l,(c,l)::s)
    in SND (FOLDR update (start_locs,[]) l)
`;

val parse_arg_def = Define`
  parse_arg s = do
    (rest,args) <- destResult (peg_exec argPEG (pnt init_NT) (add_locs s) [] done failed);
    if rest <> [] then NONE else SOME args
  od
`;

val parse_arg_list_aux = Define`
  parse_arg_list_aux [] fs      = INR (REVERSE fs) ∧
  parse_arg_list_aux (x::xs) fs =
    case parse_arg (explode x) of
        NONE   => INL (implode "Parse error on: " ^ x)
      | SOME s => parse_arg_list_aux xs (s::fs)
`;

val parse_arg_list_def = Define`
  parse_arg_list l = parse_arg_list_aux l []
`;

(* Given a configuration function (perhaps using `mkArgsConf`)
 *)
val parse_conf_def = Define`
  parse_conf conf l = case parse_arg_list l of
                          INL m    => INL m
                       |  INR args => conf (expandArgs args)
`;

val _ = export_theory()
