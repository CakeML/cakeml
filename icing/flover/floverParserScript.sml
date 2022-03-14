open AbbrevsTheory MachineTypeTheory ExpressionsTheory CommandsTheory
FloverMapTheory;
open preambleFloVer;

val _ = new_theory "floverParser";

    (*
val _ = Datatype `
  Token =
    | DLET
    | DRET
    | DPRE
    | DABS
    | DCOND
    | DGAMMA
    | DTYPE mType
    | DFIXED
    | DVAR
    | DCONST num
    | DNEG
    | DPLUS
    | DSUB
    | DMUL
    | DDIV
    | DFRAC
    | DCAST `;

val getConst_def = Define `
  getConst (c:char) = ORD c - 48`;

val lexConst_def = Define`
  lexConst (input:string) (akk:num) =
    case input of
      | STRING char input' =>
        if (isDigit char)
        then lexConst input' (akk * 10 + (getConst char))
        else (akk, input)
      |"" => (akk, input)`;

val lexName_def = Define `
  lexName (input:string) =
    case input of
     | STRING char input' =>
       if (isAlphaNum char)
       then
         let (name, input') = lexName input' in
         (STRING char name, input')
       else ("", input)
         | "" => ("",input)`;

val strSize_def = Define `
  strSize str :num=
    case str of
      | STRING _ str' => 1 + strSize str'
      | "" => 0`;

val lexName_imp = prove(
  ``!s s1 s2. lexName s = (s1,s2) ==> (s = s1 ++ s2)``,
  Induct \\ simp [Once lexName_def]
  \\ rw [] \\ pairarg_tac \\ fs []);

val lexConst_imp = prove(
  ``!s n s1 s2. lexConst s n = (s1,s2) ==> LENGTH s2 <= LENGTH s``,
  Induct \\ simp [Once lexConst_def]
  \\ rw [] \\ res_tac \\ fs []);

val lex_def = tDefine "lex" `
  lex input =
    case input of
    | STRING char input' =>
      if isDigit char
      then
        let (num, input'') = lexConst input 0 in
          DCONST num :: lex input''
      else
        if isAlpha char
        then
          let (name, input'') = lexName input in
            case name of
              | "Ret" => DRET :: lex input''
              | "Let" => DLET :: lex input''
              | "PRE" => DPRE :: lex input''
              | "ABS" => DABS :: lex input''
              | "GAMMA" => DGAMMA :: lex input''
              | "Var" => DVAR :: lex input''
              | "Cast" => DCAST :: lex input''
              | "F" => DFIXED :: lex input''
              | "MTYPE" => let ts = lex input'' in
                           (case ts of
                            | DCONST 16 :: ts' => DTYPE M16 :: ts'
                            | DCONST 32 :: ts' => DTYPE M32 :: ts'
                            | DCONST 64 :: ts' => DTYPE M64 :: ts'
                            | DFIXED :: DCONST w :: DCONST f :: ts' =>
                                DTYPE (F w f s) :: ts'
                            (* | DCONST 128 :: ts' => DTYPE M128 :: ts' *)
                            (* | DCONST 256 :: ts' => DTYPE M256 :: ts' *)
                            | _ => NIL)
              | _ => NIL
        else
          (case char of
            | #"+" => DPLUS :: lex input'
            | #"-" => DSUB  :: lex input'
            | #"*" => DMUL :: lex input'
            | #"/" => DDIV :: lex input'
            | #"#" => DFRAC :: lex input'
            | #"?" => DCOND :: lex input'
            | #"~" => DNEG :: lex input'
            | #" " => lex input'
            | #"\n" => lex input'
            | _ => NIL)
    |  _  => NIL`
 (WF_REL_TAC `measure LENGTH` \\ rw [] \\ fs []
  \\ imp_res_tac (GSYM lexName_imp) \\ fs [] \\ rveq \\ fs []
  \\ fs [Once lexConst_def] \\ rfs []
  \\ imp_res_tac (GSYM lexConst_imp) \\ fs [] \\ rveq \\ fs []);

val str_join_def = Define `
  (str_join (STRING c s1) s2 = STRING c (str_join s1 s2)) /\
  (str_join "" s2 = s2)`;

val str_of_num_def = Define `
  str_of_num (n:num) =
    if n < 10 then STRING (CHR (n + 48)) ""
    else str_join (str_of_num (n DIV 10)) (STRING (CHR ( (n MOD 10) + 48)) "")`

val str_of_bool_def = Define ‘
                       str_of_bool (b:bool) = if b then "T" else "F"’

val type_to_string = Define `
  (type_to_string (M16) = "MTYPE 16") /\
  (type_to_string (M32) = "MTYPE 32") /\
  (type_to_string (M64) = "MTYPE 64") /\
  (type_to_string (F w f s) =
    str_join "MTYPE "
      (str_join ("F ")
      (str_join (str_of_num w)
      (str_join " "
      (str_join (str_of_num f)
      (str_join " "
      (str_of_bool s)))))))`; (* FIXME *)
  (* (type_to_string (M128) = "MTYPE 128") /\ *)
  (* (type_to_string (M256) = "MTYPE 256")`; *)

val pp_token_def = Define `
  pp_token (token:Token) =
    case token of
    | DLET => "Let"
    | DRET => "Ret"
    | DPRE => "PRE"
    | DABS => "ABS"
    | DCOND => "?"
    | DVAR => "Var"
    | DCONST num => str_of_num num
    | DGAMMA => "GAMMA"
    | DTYPE m => type_to_string m
    | DFIXED => ""
    | DNEG => "~"
    | DPLUS => "+"
    | DSUB => "-"
    | DMUL => "*"
    | DDIV => "/"
    | DFRAC => "#"
    | DCAST => "Cast"`;

(* val pp_token_correct = store_thm ("pp_token_correct", *)
(*   ``!t. lex (pp_token t) = [t]``, *)
(*  Induct_on `t`  \\ EVAL_TAC fs[pp_token_def, lex_def] *)
(* ); *)

(* val str_join_empty = store_thm ("str_join_empty", *)
(*   ``!s. str_join s "" = s``, *)
(*   Induct \\ fs[str_join_def]); *)

(* Pretty Printer for Tokens *)
val pp_def = Define `
  (pp (token :: tokList) = str_join (pp_token token) (pp tokList)) /\
  (pp NIL = "")`;

(* val lex_thm = prove ( *)
(*   ``!s. *)
(*     lex (pp (lex s)) = lex s``, *)
(*   measureInduct_on `STRLEN s` \\ Cases_on `s` *)
(*   >- (EVAL_TAC) *)
(*   >- (qspec_then `STRING h t` (fn thm => rw [Once thm]) lex_def *)
(*       >- (simp[Once lexConst_def] *)
(*           \\ qspec_then `STRING h t` (fn thm => rw [Once thm]) lex_def *)
(*           \\ qspec_then `STRING h t` (fn thm => simp[Once thm]) lexConst_def *)
(*           \\ Cases_on `lexConst t (getConst h)` \\ fs[] *)
(*           \\ `STRLEN r < SUC (STRLEN t)` by cheat *)
(*           \\ first_x_assum drule *)
(*           \\ disch_then assume_tac *)
(*           \\ fs[Once pp_def] *)
(*           \\ fs [Once pp_token_def] *)
(*           \\ cheat) *)
(*       >- (qspec_then `STRING h t` (fn thm => rw [Once thm]) lex_def *)
(*           \\ Cases_on `lexName (STRING h t)` \\ fs[] *)
(*           \\ Cases_on `q` \\ fs[] \\ TRY (EVAL_TAC) *)
(*           \\ fs[] *)
(*           \\ cheat) *)
(*       >- (rw [Once pp_def, Once str_join_def, pp_token_def, Once str_join_def, Once lex_def] *)
(*           \\ qspec_then `STRING #"+" s` (fn thm => rw [Once thm]) lex_def) *)
(*       >- (rw [Once pp_def, Once str_join_def, pp_token_def, Once str_join_def, Once lex_def] *)
(*           \\ qspec_then `STRING #"-" s` (fn thm => rw [Once thm]) lex_def) *)
(*       >- (rw [Once pp_def, Once str_join_def, pp_token_def, Once str_join_def, Once lex_def] *)
(*           \\ qspec_then `STRING #"*" s` (fn thm => rw [Once thm]) lex_def) *)
(*       >- (rw [Once pp_def, Once str_join_def, pp_token_def, Once str_join_def, Once lex_def] *)
(*           \\ qspec_then `STRING #"/" s` (fn thm => rw [Once thm]) lex_def) *)
(*       >- (rw [Once pp_def, Once str_join_def, pp_token_def, Once str_join_def, Once lex_def] *)
(*           \\ qspec_then `STRING #"#" s` (fn thm => rw [Once thm]) lex_def) *)
(*       >- (rw [Once pp_def, Once str_join_def, pp_token_def, Once str_join_def, Once lex_def] *)
(*           \\ qspec_then `STRING #"?" s` (fn thm => rw [Once thm]) lex_def) *)
(*       >- (rw [Once pp_def, Once str_join_def, pp_token_def, Once str_join_def, Once lex_def] *)
(*           \\ qspec_then `STRING #"~" s` (fn thm => rw [Once thm]) lex_def) *)
(*       >- (qspec_then `STRING #" " s` (fn thm => rw [Once thm]) lex_def) *)
(*       >- (qspec_then `STRING #"\n" s` (fn thm => rw [Once thm]) lex_def) *)
(*       >- (qspec_then `STRING h s` (fn thm => rw [Once thm]) lex_def *)
(*           \\ rw [Once pp_def, Once lex_def]))); *)

val fix_res_def = Define `
  fix_res xs NONE = NONE /\
  fix_res xs (SOME (x,y)) =
    if LENGTH xs < LENGTH y then SOME (x,xs) else SOME (x,y)`

val fix_res_imp = prove(
  ``fix_res xs a = SOME (x,y) ==> LENGTH y <= LENGTH xs``,
  Cases_on `a` \\ rw [fix_res_def]
  \\ Cases_on `x'` \\ fs [fix_res_def]
  \\ every_case_tac \\ fs [] \\ rveq \\ fs []);

(** Prefix form parser for exprressions **)
val parseExp_def = tDefine "parseExp" `
  parseExp (tokList:Token list) :(real expr # Token list) option =
    case tokList of
    | DCONST n :: DFRAC :: DCONST m :: DTYPE t :: tokRest =>
      if (m = 0) then NONE else SOME (Const t ((&n):real / &m), tokRest)
    | DVAR :: DCONST n :: tokRest => SOME (Var n, tokRest)
    | DNEG :: tokRest =>
      (case (parseExp tokRest) of
         | SOME (Const t c, tokRest) => SOME (Const t (- c), tokRest)
         | SOME (e1,tokRest') => SOME (Unop Neg e1, tokRest')
         | NONE => NONE)
    | DPLUS :: tokRest =>
      (case fix_res tokRest (parseExp tokRest) of
         | SOME (e1,tokRest') =>
           (case (parseExp tokRest') of
              | SOME (e2, tokRest'') => SOME (Binop Plus e1 e2, tokRest'')
              | NONE => NONE)
         | NONE => NONE)
    | DSUB :: tokRest =>
      (case fix_res tokRest (parseExp tokRest) of
         | SOME (e1,tokRest') =>
           (case (parseExp tokRest') of
              | SOME (e2, tokRest'') => SOME (Binop Sub e1 e2, tokRest'')
              | NONE => NONE)
         | NONE => NONE)
    | DMUL :: tokRest =>
      (case fix_res tokRest (parseExp tokRest) of
         | SOME (e1,tokRest') =>
           (case (parseExp tokRest') of
              | SOME (e2, tokRest'') => SOME (Binop Mult e1 e2, tokRest'')
              | NONE => NONE)
         | NONE => NONE)
    | DDIV :: tokRest =>
      (case fix_res tokRest (parseExp tokRest) of
         | SOME (e1,tokRest') =>
           (case (parseExp tokRest') of
              | SOME (e2, tokRest'') => SOME (Binop Div e1 e2, tokRest'')
              | NONE => NONE)
         | NONE => NONE)
    | DCAST :: DTYPE m :: tokRest =>
      (case fix_res tokRest (parseExp tokRest) of
         | SOME (e1, tokRest') => SOME (Downcast m e1,tokRest')
         | _ => NONE)
    | _ => NONE`
 (WF_REL_TAC `measure LENGTH`
  \\ rw [] \\ fs []
  \\ imp_res_tac fix_res_imp \\ fs []);

val parseExp_ind = fetch "-" "parseExp_ind";

val parseExp_LESS_EQ = prove(
  ``!xs x y. parseExp xs = SOME (x,y) ==> LENGTH y <= LENGTH xs``,
  recInduct parseExp_ind
  \\ rw [] \\ fs [] \\ pop_assum mp_tac
  \\ once_rewrite_tac [parseExp_def]
  \\ ntac 8 (TRY (TOP_CASE_TAC \\ fs [])) \\ rw []
  \\ fs [] \\ imp_res_tac fix_res_imp \\ fs [])

val fix_res_parseExp = prove(
  ``fix_res xs (parseExp xs) = parseExp xs``,
  Cases_on `parseExp xs` \\ fs [fix_res_def]
  \\ Cases_on `x` \\ fs [fix_res_def]
  \\ imp_res_tac parseExp_LESS_EQ \\ fs []);

val parseExp_def = save_thm("parseExp_def",
  parseExp_def |> REWRITE_RULE [fix_res_parseExp]);

val parseExp_ind = save_thm("parseExp_ind",
  parseExp_ind |> REWRITE_RULE [fix_res_parseExp]);

val parseRet_def = Define `
  parseRet input :(real cmd # Token list) option =
    case parseExp input of
     | SOME (e, tokRest) => SOME (Ret e, tokRest)
     | NONE => NONE`;

val parseLet_def = tDefine "parseLet" `
  parseLet input :(real cmd # Token list) option =
    case input of
     (* We have a valid let binding *)
     | DVAR :: DCONST n :: DTYPE m :: exprLetRest =>
       (* so we parse an exprression *)
       (case parseExp exprLetRest of
          | SOME (e, letRest) =>
            (case letRest of
               (* If we continue with a let *)
               | DLET :: letBodyRest =>
                 (* Parse it *)
                 (case (parseLet letBodyRest) of
                    (* And construct a result from it *)
                    | SOME (letCmd, arbRest) => SOME (Let m n e letCmd, arbRest)
                    | _ => NONE)
               (* But if we have a return *)
               | DRET :: retBodyRest =>
                 (* parse only this *)
                 (case (parseRet retBodyRest) of
                    (* and construct the result *)
                    | SOME (retCmd, arbRest) => SOME (Let m n e retCmd, arbRest)
                    | _ => NONE)
               | _ => NONE) (* fail if there is no continuation for the let *)
          | NONE => NONE) (* fail if we do not have an exprression to bind *)
     | _ => NONE` (* fail if we cannot find a variable *)
  (WF_REL_TAC `measure LENGTH`
   \\ rw [] \\ imp_res_tac fix_res_imp \\ fs []
   \\ imp_res_tac parseExp_LESS_EQ \\ fs [])

val parseLet_ind = fetch "-" "parseLet_ind";

val parseFrac_def = Define `
  parseFrac (input:Token list) :(real # Token list) option =
     case input of
      | DNEG :: DCONST n :: DFRAC :: DCONST m :: tokRest =>
        if (m = 0) then NONE else SOME ((- &n):real / (&m),tokRest)
      | DCONST n :: DFRAC :: DCONST m :: tokRest =>
        if (m = 0) then NONE else SOME ((&n):real / (&m),tokRest)
      | _ => NONE `;

val parseIV_def = Define `
  parseIV (input:Token list) :(interval # Token list) option =
    case (parseFrac input) of
      | SOME (iv_lo, tokRest) =>
        (case (parseFrac tokRest) of
           | SOME (iv_hi, tokList) => SOME ((iv_lo, iv_hi), tokList)
           | _ => NONE )
      | _ => NONE`;

val defaultPre_def = Define
  `defaultPre:precond = \x. (0,0)`;

val updPre_def = Define
  `updPre (n:num) (iv:interval) (P:precond) =
     \m. if (n = m) then iv else P m`;

val parseFrac_LESS_EQ = prove(
  ``parseFrac xs = SOME (x,y) ==> LENGTH y <= LENGTH xs``,
  fs [parseFrac_def] \\ every_case_tac \\ fs []);

val parseIV_LESS_EQ = prove(
  ``parseIV xs = SOME (x,y) ==> LENGTH y <= LENGTH xs``,
  fs [parseIV_def] \\ every_case_tac \\ fs []
  \\ imp_res_tac parseFrac_LESS_EQ \\ fs [] \\ rw [] \\ fs []);

(** Precondition parser: *)
(*   The precondition should be encoded in the following format: *)
(*   PRECOND ::= DCOND DVAR DCONST FRACTION FRACTION PRECOND | EPSILON *)
(*   The beginning of the precondition is marked by the DPRE token *)
(* **)
val parsePrecondRec_def = tDefine "parsePrecondRec" `
  parsePrecondRec (input:Token list) :(precond # Token list) option =
    (case input of
       | DCOND :: DVAR :: DCONST n :: fracRest =>
         (case parseIV fracRest of
            | SOME (iv, precondRest) =>
              (case parsePrecondRec precondRest of
                 | SOME (P, tokRest) => SOME (updPre n iv P, tokRest)
                 | NONE => SOME (updPre n iv defaultPre, precondRest))
            | _ => NONE)
       | _ => NONE) `
  (WF_REL_TAC `measure LENGTH` \\ rw []
   \\ imp_res_tac parseIV_LESS_EQ \\ fs []);

val parsePrecond_def = Define `
  parsePrecond (input :Token list) =
    case input of
    | DPRE :: tokRest => parsePrecondRec tokRest
    | _ => NONE`;

val defaultAbsenv_def = Define
  `defaultAbsenv:analysisResult = FloverMapTree_empty`;

val updAbsenv_def = Define
  `updAbsenv (e:real expr) (iv:interval) (err:real) (A:analysisResult) =
     FloverMapTree_insert e (iv,err) A`;

(** Abstract environment parser: *)
(*   The abstract environment should be encoded in the following format: *)
(*   ABSENV ::= ? EXPRESSION FRACTION FRACTION FRACTION ABSENV | EPSILON *)
(*   The beginning of the abstract environment is marked by the DABS token *)
(* **)
val parseAbsEnvRec_def = tDefine "parseAbsEnvRec" `
  parseAbsEnvRec (input:Token list) :(analysisResult # Token list) option =
    (case input of
       | DCOND :: exprRest =>
         (case parseExp exprRest of
            | SOME (e,fracRest) =>
              (case parseIV fracRest of
                 | SOME (iv, errRest) =>
                   (case parseFrac errRest of
                      | SOME (err, absenvRest) =>
                        (case parseAbsEnvRec absenvRest of
                           | SOME (A, tokRest) => SOME (updAbsenv e iv err A, tokRest)
                           | NONE => SOME (updAbsenv e iv err defaultAbsenv, absenvRest))
                      | NONE => NONE)
                 | _ => NONE)
              | NONE => NONE)
       | _ => SOME (defaultAbsenv, input))`
  (WF_REL_TAC `measure LENGTH` \\ rw []
   \\ imp_res_tac parseFrac_LESS_EQ
   \\ imp_res_tac parseIV_LESS_EQ
   \\ imp_res_tac parseExp_LESS_EQ
   \\ fs []);

val parseAbsEnv_def = Define `
  parseAbsEnv (input:Token list) =
    case input of
    | DABS :: tokRest => parseAbsEnvRec tokRest
    | _ => NONE`;

val defaultGamma_def = Define `
  defaultGamma:mType fMap = FloverMapTree_empty`;

val parseGammaRec_def = tDefine "parseGammaRec"
  `parseGammaRec (input: Token list) : (typeMap # Token list) option =
    (case parseExp input of
      |NONE => SOME (defaultGamma, input)
      |SOME (e,residual) =>
        (case residual of
         | DTYPE m :: inputRest =>
          (case parseGammaRec inputRest of
            | SOME (Gamma, rest) =>
              SOME (FloverMapTree_insert e m Gamma, rest)
            | NONE => NONE)
         | _ => SOME (defaultGamma, input)))`
  (WF_REL_TAC `measure LENGTH` \\ rw[]
  \\ IMP_RES_TAC parseExp_LESS_EQ
  \\ fs[]);

val parseGamma_def = Define `
  parseGamma (input:Token list) =
      case input of
       | DGAMMA :: tokenRest => parseGammaRec tokenRest
       | _ => NONE`;

(* Global parsing function*)
val dParse_def = Define `
  dParse (input:Token list) =
    let cmdParse =
      (case input of
        | DLET :: tokRest => parseLet tokRest
        | DRET :: tokRest => parseRet tokRest
        | _ => NONE) in
    case cmdParse of
      |NONE => NONE
      | SOME (dCmd, tokRest) =>
      (case parseGamma tokRest of
      |NONE => NONE
      |SOME (Gamma, residual) =>
        (case parsePrecond residual of
        |NONE => NONE
        |SOME (P, residual) =>
          (case parseAbsEnv residual of
          |NONE => NONE
          |SOME (A, residual) =>
              SOME ((dCmd, P, A, Gamma), residual))))`;
    *)

val _ = export_theory();
