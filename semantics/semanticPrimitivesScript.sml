(*
  Definitions of semantic primitives (e.g., values, and functions for doing
  primitive operations) used in the semantics.
*)
open HolKernel Parse boolLib bossLib;
open libTheory astTheory namespaceTheory ffiTheory fpValTreeTheory fpSemTheory realOpsTheory;

val _ = numLib.prefer_num();

val _ = new_theory "semanticPrimitives"

(* Constructors and exceptions need unique identities, which we represent by stamps. *)
Datatype:
 stamp =
  (* Each type gets a unique number, and the constructor name must be unique
     inside of the type *)
    TypeStamp conN num
  | ExnStamp num
End

Datatype:
  sem_env =
  <| v : (modN, varN, 'v) namespace
   (* Lexical mapping of constructor idents to arity, stamp pairs *)
   ; c : (modN, conN, (num # stamp)) namespace
   |>
End

(* Value forms *)
Datatype:
 v =
    Litv lit
  (* Constructor application. Can be a tuple or a given constructor of a given type *)
  | Conv (stamp option) (v list)
  (* Function closures
     The environment is used for the free variables in the function *)
  | Closure (v sem_env) varN exp
  (* Function closure for recursive functions
   * See Closure and Letrec above
   * The last variable name indicates which function from the mutually
   * recursive bundle this closure value represents *)
  | Recclosure (v sem_env) ((varN # varN # exp) list) varN
  | Loc num
  | Vectorv (v list)
  | FP_WordTree fp_word_val
  | FP_BoolTree fp_bool_val
  | Real real
  (* Environment value for Eval, and its numeric identifier *)
  | Env (v sem_env) (num # num)
End

(* The runtime semantics should be able to deal with constants too, thus we add
   a translation function from word constants to value trees *)
(*val fp_translate: v -> maybe v*)
Definition fp_translate_def:
  fp_translate (Litv (Word64 w)) = (SOME (FP_WordTree (Fp_const w))) ∧
  fp_translate (FP_WordTree v) = (SOME (FP_WordTree v)) ∧
  fp_translate (FP_BoolTree v) = (SOME (FP_BoolTree v)) ∧
  fp_translate _=  NONE
End

Type env_ctor = ``: (modN, conN, (num # stamp)) namespace``
Type env_val = ``: (modN, varN, v) namespace``

val _ = Define ‘bind_stamp = ExnStamp 0’
val _ = Define ‘chr_stamp = ExnStamp 1’
val _ = Define ‘div_stamp = ExnStamp 2’
val _ = Define ‘subscript_stamp = ExnStamp 3’

val _ = Define ‘bind_exn_v = Conv (SOME bind_stamp) []’
val _ = Define ‘chr_exn_v = Conv (SOME chr_stamp) []’
val _ = Define ‘div_exn_v = Conv (SOME div_stamp) []’
val _ = Define ‘sub_exn_v = Conv (SOME subscript_stamp) []’

val _ = Define ‘bool_type_num   = 0’
val _ = Define ‘list_type_num   = 1’
val _ = Define ‘option_type_num = 2’
val _ = Define ‘lit_type_num    = 3’
val _ = Define ‘id_type_num     = 4’
val _ = Define ‘ast_t_type_num  = 5’
val _ = Define ‘pat_type_num    = 6’
val _ = Define ‘lop_type_num    = 7’
val _ = Define ‘opn_type_num    = 8’
val _ = Define ‘opb_type_num    = 9’
val _ = Define ‘opw_type_num    = 10’
val _ = Define ‘shift_type_num  = 11’
val _ = Define ‘word_size_type_num = 12’
val _ = Define ‘fp_uop_type_num = 13’
val _ = Define ‘fp_bop_type_num = 14’
val _ = Define ‘fp_top_type_num = 15’
val _ = Define ‘fp_cmp_type_num = 16’
val _ = Define ‘real_uop_type_num = 17’
val _ = Define ‘real_bop_type_num = 18’
val _ = Define ‘real_cmp_type_num = 19’
val _ = Define ‘op_type_num     = 20’
val _ = Define ‘locn_type_num   = 21’
val _ = Define ‘locs_type_num   = 22’
val _ = Define ‘fp_opt_num      = 23’
val _ = Define ‘exp_type_num    = 24’
val _ = Define ‘dec_type_num    = 25’

(* The result of evaluation *)
Datatype:
  abort =
     Rtype_error
   | Rtimeout_error
   | Rffi_error final_event
End

Datatype:
  error_result =
     Rraise 'a (* Should only be a value of type exn *)
   | Rabort abort
End

Datatype:
  result =
     Rval 'a
   | Rerr ('b error_result)
End

(* Stores *)
Datatype:
 store_v =
  (* A ref cell *)
    Refv 'a
  (* A byte array *)
  | W8array (word8 list)
  (* An array of values *)
  | Varray ('a list)
End

Definition store_v_same_type_def:
  store_v_same_type v1 v2 =
    case (v1:'a store_v, v2:'a store_v) of
    | (Refv _, Refv _) => T
    | (W8array _,W8array _) => T
    | (Varray _,Varray _) => T
    | _ => F
End

(* The nth item in the list is the value at location n *)
Type store = “:('a store_v) list”

val _ = Define ‘empty_store = []:α store_v list’

Definition store_lookup_def:
  store_lookup l (st:('a store_v) list) =
    if l < LENGTH st then SOME (EL l st) else NONE
End

Definition store_alloc_def:
  store_alloc (v:'a store_v) st = (st ++ [v],LENGTH st)
End

Definition store_assign_def:
  store_assign n (v:'a store_v) st =
    if n < LENGTH st ∧ store_v_same_type (EL n st) v then
      SOME (LUPDATE v n st)
    else NONE
End

(* Compiler checker for Eval. The current design requires the compiler
   to be run (as regular code within the semantics) before Eval is called,
   and these config parameters specify how to interpret the declarations to
   be evaluated and check that the compiler was run correctly.

   Before attempting build a state of this type, find out about
   mk_init_eval_state in source_evalProof.
*)
Type compiler_args = ``: ((num # num) # v # dec list)``
Type compiler_fun = ``: compiler_args ->
     (v # word8 list # word64 list)option``

(*
   State component encapsulating Icing optimizations and rewriter oracle.
   rws := list of rewrites allowed to be applied by the semantics
   opts := oracle that decides which rewrites are applied next
   choices := global counter how many rewriting steps have been done
   canOpt := flag indicating whether evaluation has stepped below an "opt" scope
*)
Datatype:
 optChoice =
    Strict (* strict 64-bit floating-point semantics, ignores annotations *)
 | FPScope fp_opt (* currently under scope *)
End

Datatype:
 fpState =
  <| rws: fp_rw list
   ; opts: num -> rewrite_app list
   ; choices: num
   ; canOpt : optChoice
   ; real_sem : bool
   |>
End

Datatype:
 eval_decs_state =
  <|
    compiler : compiler_fun ;
    (* state must be encoded as v somehow *)
    compiler_state : v ;
    env_id_counter : (num # num # num) ;
    (* decs must also be encoded as v *)
    decode_decs : v ->  ( dec list)option
  |>
End

(* Alternative mode for Eval including an oracle.
   This is only for use in the compiler proof. *)
Type eval_oracle_fun = ``: num -> compiler_args``

Datatype:
 eval_oracle_state =
  <|
    oracle : eval_oracle_fun ;
    custom_do_eval : v list -> eval_oracle_fun ->
         ((num # num) # eval_oracle_fun # dec list)option ;
    envs : ( ( v sem_env)list) list ;
    generation : num
  |>
End

Datatype:
  eval_state =
     EvalDecs eval_decs_state
   | EvalOracle eval_oracle_state
End

Datatype:
  state =
  <| clock : num
   ; refs  : v store
   ; ffi : 'ffi ffi_state
   ; next_type_stamp : num
   ; next_exn_stamp : num
   ; fp_state : fpState
   ; eval_state :  eval_state option
   |>
End

(* Other primitives *)
(* Check that a constructor is properly applied *)
Definition do_con_check_def:
  do_con_check (cenv:((string),(string),(num#stamp))namespace) n_opt l ⇔
    case n_opt of
      NONE => T
    | SOME n => case nsLookup cenv n of NONE => F | SOME (l',v2) => l = l'
End

Definition one_con_check_def[simp]:
  one_con_check envc (Con cn es) = do_con_check envc cn (LENGTH es) ∧
  one_con_check envc _ = T
End

Definition build_conv_def:
  build_conv (envC:((string),(string),(num#stamp))namespace) cn vs =
  case cn of
    NONE => SOME (Conv NONE vs)
  | SOME id =>
      case nsLookup envC id of
        NONE => NONE
      | SOME (len,stamp) => SOME (Conv (SOME stamp) vs)
End

Definition lit_same_type_def:
  lit_same_type l1 l2 ⇔
     case (l1,l2) of
     | (IntLit _, IntLit _) => T
     | (Char   _, Char   _) => T
     | (StrLit _, StrLit _) => T
     | (Word8  _, Word8  _) => T
     | (Word64 _, Word64 _) => T
     | _ => F
End

Datatype:
  match_result =
     No_match
   | Match_type_error
   | Match 'a
End

Definition same_type_def:
  (same_type (TypeStamp v0 n1) (TypeStamp v1 n2) ⇔ n1 = n2) ∧
  (same_type (ExnStamp v2) (ExnStamp v3) ⇔ T) ∧
  (same_type _ _ ⇔ F)
End

Definition same_ctor_def:
  same_ctor stamp1 stamp2 ⇔ stamp1 = (stamp2:stamp)
End

Definition ctor_same_type_def:
  ctor_same_type c1 c2 ⇔
   case (c1,c2) of
     (NONE,NONE) => T
   | (SOME stamp1,SOME stamp2) => same_type stamp1 stamp2
   | _ => F
End

Definition Boolv_def:
  Boolv b =
    if b then Conv (SOME (TypeStamp "True" bool_type_num)) []
         else Conv (SOME (TypeStamp "False" bool_type_num)) []
End

Definition compress_def:
 compress (FP_WordTree fp) = (Litv (Word64 (compress_word fp))) ∧
 compress (FP_BoolTree fp) = (Boolv (compress_bool fp)) ∧
 compress (Real r) = (Real r) ∧
 compress (Litv l) =  (Litv l) ∧
 compress (Conv ts vs) = (Conv ts (compress_list vs)) ∧
 compress (Closure env x e) = (Closure env x e) ∧
 compress (Env env n) =  (Env env n) ∧
 compress (Recclosure env es x) = (Recclosure env es x) ∧
 compress (Loc n) =  (Loc n) ∧
 compress (Vectorv vs) = (Vectorv (compress_list vs)) ∧
 compress_list [] = [] ∧
 compress_list (v::vs) = (compress v)::(compress_list vs)
End

(* A big-step pattern matcher.  If the value matches the pattern, return an
 * environment with the pattern variables bound to the corresponding sub-terms
 * of the value; this environment extends the environment given as an argument.
 * No_match is returned when there is no match, but any constructors
 * encountered in determining the match failure are applied to the correct
 * number of arguments, and constructors in corresponding positions in the
 * pattern and value come from the same type.  Match_type_error is returned
 * when one of these conditions is violated *)
Definition pmatch_def:
  pmatch envC s Pany v' env = Match env ∧
  pmatch envC s (Pvar x) v' env = Match ((x,v')::env) ∧
  pmatch envC s (Plit l) (Litv l') env =
  (if l = l' then Match env
   else if lit_same_type l l' then No_match
   else Match_type_error) ∧
  pmatch envC s (Pcon (SOME n) ps) (Conv (SOME stamp') vs) env =
  (case nsLookup envC n of
     NONE => Match_type_error
   | SOME (l,stamp) =>
       if same_type stamp stamp' ∧ LENGTH ps = l then
         if same_ctor stamp stamp' then
           if LENGTH vs = l then pmatch_list envC s ps vs env
           else Match_type_error
         else No_match
       else Match_type_error) ∧
  pmatch envC s (Pcon NONE ps) (Conv NONE vs) env =
  (if LENGTH ps = LENGTH vs then pmatch_list envC s ps vs env
   else Match_type_error) ∧
  pmatch envC s (Pref p) (Loc lnum) env =
  (case store_lookup lnum s of
     NONE => Match_type_error
   | SOME (Refv v) => pmatch envC s p v env
   | SOME (W8array v6) => Match_type_error
   | SOME (Varray v7) => Match_type_error) ∧
  pmatch envC s (Pas p i) v env = pmatch envC s p v ((i,v)::env) ∧
  pmatch envC s (Ptannot p t) v env = pmatch envC s p v env ∧
  pmatch envC s _ _ env = Match_type_error ∧
  pmatch_list envC s [] [] env = Match env ∧
  pmatch_list envC s (p::ps) (v::vs) env =
  (case pmatch envC s p v env of
     No_match =>
       (case pmatch_list envC s ps vs env of
          No_match => No_match
        | Match_type_error => Match_type_error
        | Match v1 => No_match)
   | Match_type_error => Match_type_error
   | Match env' => pmatch_list envC s ps vs env') ∧
  pmatch_list envC s _ _ env = Match_type_error
Termination
  WF_REL_TAC
  `inv_image $< (λx. case x of INL (s,a,p,b,c) => pat_size p
                            | INR (s,a,ps,b,c) => list_size pat_size ps)`
End

Definition can_pmatch_all_def:
  (can_pmatch_all envC refs [] v ⇔ T) ∧
  (can_pmatch_all envC refs (p::ps) v ⇔
     if pmatch envC refs p v [] = Match_type_error then F
     else can_pmatch_all envC refs ps v)
End

(* Bind each function of a mutually recursive set of functions to its closure *)
Definition build_rec_env_def:
  (build_rec_env:(varN#varN#exp)list ->(v)sem_env ->((string),(string),(v))namespace
                 ->((string),(string),(v))namespace) funs cl_env add_to_env =
  FOLDR (λ(f,x,e) env'. nsBind f (Recclosure cl_env funs f) env')
        add_to_env funs
End

(* Lookup in the list of mutually recursive functions *)
Definition find_recfun_def:
  (find_recfun:string ->(string#'a#'b)list ->('a#'b)option) n funs =
  case funs of
    [] => NONE
  | (f,x,e)::funs' => if f = n then SOME (x,e) else find_recfun n funs'
End

Datatype:
  eq_result =
     Eq_val bool
   | Eq_type_error
End

Definition do_eq_def:
  do_eq (Litv l1) (Litv l2) =
    (if lit_same_type l1 l2 then Eq_val (l1 = l2) else Eq_type_error) ∧
  do_eq (Loc l1) (Loc l2) = Eq_val (l1 = l2) ∧
  do_eq (Conv cn1 vs1) (Conv cn2 vs2) =
    (if cn1 = cn2 ∧ LENGTH vs1 = LENGTH vs2 then do_eq_list vs1 vs2
     else if ctor_same_type cn1 cn2 then Eq_val F
     else Eq_type_error) ∧
  do_eq (Vectorv vs1) (Vectorv vs2) =
    (if LENGTH vs1 = LENGTH vs2 then do_eq_list vs1 vs2 else Eq_val F) ∧
  do_eq (Closure v0 v3 v4) (Closure v5 v6 v7) = Eq_val T ∧
  do_eq (Closure v8 v9 v10) (Recclosure v11 v12 v13) = Eq_val T ∧
  do_eq (Recclosure v14 v15 v16) (Closure v17 v18 v19) = Eq_val T ∧
  do_eq (Recclosure v20 v21 v22) (Recclosure v23 v24 v25) = Eq_val T ∧
  do_eq (FP_BoolTree v1) (FP_BoolTree v2) = (Eq_val (compress_bool v1 <=> compress_bool v2)) ∧
  do_eq (FP_BoolTree v1) (Conv cn2 vs2)=
   (case Boolv (compress_bool v1) of
    Conv cn1 vs1 =>
    if (cn1 = cn2) /\ (LENGTH vs1 = LENGTH vs2) then
      do_eq_list vs1 vs2
      else if ctor_same_type cn1 cn2 then
         Eq_val F
      else
        Eq_type_error
  | _ => Eq_type_error) ∧
  do_eq (Conv cn1 vs1) (FP_BoolTree v2)=
   (case Boolv (compress_bool v2) of
    Conv cn2 vs2 =>
    if (cn1 = cn2) /\ (LENGTH vs1 = LENGTH vs2) then
      do_eq_list vs1 vs2
      else if ctor_same_type cn1 cn2 then
         Eq_val F
      else
        Eq_type_error
  | _ => Eq_type_error) ∧
  do_eq (FP_WordTree v1) (FP_WordTree v2) = (Eq_val (compress_word v1 = compress_word v2)) ∧
  do_eq (Litv (Word64 w1)) (FP_WordTree v2) = (Eq_val (w1 = compress_word v2)) ∧
  do_eq (FP_WordTree v1) (Litv (Word64 w2)) = (Eq_val (compress_word v1 = w2)) ∧
  do_eq (Real r1) (Real r2) =  (Eq_val (r1 = r2)) ∧
  do_eq (Env v26 (gen1,id1)) (Env v27 (gen2,id2)) =
    Eq_val (gen1 = gen2 ∧ id1 = id2) ∧
  do_eq _ _ = Eq_type_error ∧
  do_eq_list [] [] = Eq_val T ∧
  do_eq_list (v1::vs1) (v2::vs2) =
    (case do_eq v1 v2 of
       Eq_val r => if ¬r then Eq_val F else do_eq_list vs1 vs2
     | Eq_type_error => Eq_type_error) ∧
  do_eq_list _ _ = Eq_val F
Termination
  WF_REL_TAC `inv_image $< (λx. case x of INL (v1,v2) => v_size v1
                                        | INR (vs1,vs2) => list_size v_size vs1)`
  >> Cases_on ‘compress_bool v1’ >> gs[Boolv_def, listTheory.list_size_def]
End

(* Do an application *)
Definition do_opapp_def:
  do_opapp vs =
     case vs of
     | [Closure env n e; v] => SOME (env with v := nsBind n v env.v,e)
     | [Recclosure env' funs n'; v] =>
       if ALL_DISTINCT (MAP (λ(f,x,e). f) funs) then
         case find_recfun n' funs of
           NONE => NONE
         | SOME (n,e) =>
           SOME
             (env' with v := nsBind n v (build_rec_env funs env' env'.v),e)
       else NONE
     | _ => NONE
End

(* If a value represents a list, get that list. Otherwise return Nothing *)
Definition v_to_list_def:
  v_to_list (Conv (SOME stamp) []) =
    (if stamp = TypeStamp "[]" list_type_num then SOME [] else NONE) ∧
  v_to_list (Conv (SOME stamp) [v1; v2]) =
    (if stamp = TypeStamp "::" list_type_num then
       case v_to_list v2 of NONE => NONE | SOME vs => SOME (v1::vs)
     else NONE) ∧
  v_to_list _ = NONE
End

Definition list_to_v_def:
  list_to_v [] = Conv (SOME (TypeStamp "[]" list_type_num)) [] ∧
  list_to_v (x::xs) = Conv (SOME (TypeStamp "::" list_type_num)) [x; list_to_v xs]
End

Definition v_to_char_list_def:
  v_to_char_list (Conv (SOME stamp) []) =
    (if stamp = TypeStamp "[]" list_type_num then SOME "" else NONE) ∧
  v_to_char_list (Conv (SOME stamp) [Litv (Char c); v]) =
    (if stamp = TypeStamp "::" list_type_num then
       case v_to_char_list v of NONE => NONE | SOME cs => SOME (STRING c cs)
     else NONE) ∧
  v_to_char_list _ = NONE
End

Definition vs_to_string_def:
  vs_to_string [] = SOME "" ∧
  vs_to_string (Litv (StrLit s1)::vs) =
    (case vs_to_string vs of NONE => NONE | SOME s2 => SOME (STRCAT s1 s2)) ∧
  vs_to_string (_::v1) = NONE
End

Definition maybe_to_v_def:
  maybe_to_v NONE = Conv (SOME (TypeStamp "None" option_type_num)) [] ∧
  maybe_to_v (SOME v) = Conv (SOME (TypeStamp "Some" option_type_num)) [v]
End

Definition v_to_id_def:
  v_to_id (Conv (SOME stamp) [Litv (StrLit s)]) =
     (if stamp = TypeStamp "Short" id_type_num then
        SOME (Short s)
      else NONE) ∧
  v_to_id (Conv (SOME stamp) [Litv (StrLit s); v]) =
     (if stamp = TypeStamp "Long" id_type_num then
        case v_to_id v of NONE => NONE | SOME id => SOME (Long s id)
      else NONE) ∧
  v_to_id _ = NONE
End

Definition nat_to_v_def:
  nat_to_v n = Litv (IntLit (&n))
End

Definition maybe_all_list_def:
  maybe_all_list v =
    case v of
      [] => SOME []
    | NONE::vs => NONE
    | SOME x::vs =>
        case maybe_all_list vs of NONE => NONE | SOME xs => SOME (x::xs)
End

Definition v_to_word8_def:
  v_to_word8 v =
    case v of
    | Litv (Word8 w) => SOME w
    | _ => NONE
End

Definition v_to_word8_list_def:
  v_to_word8_list v =
    case v_to_list v of
    | NONE => NONE
    | SOME xs => maybe_all_list (MAP v_to_word8 xs)
End

Definition v_to_word8_list_def:
  v_to_word8_list v =
    case v_to_list v of
    | NONE => NONE
    | SOME xs => maybe_all_list (MAP v_to_word8 xs)
End

Definition v_to_word64_def:
  v_to_word64 v =
    case v of
    | Litv (Word64 w) => SOME w
    | _ => NONE
End

Definition v_to_word64_list_def:
  v_to_word64_list v =
    case v_to_list v of
    | NONE => NONE
    | SOME xs => maybe_all_list (MAP v_to_word64 xs)
End

Definition lookup_env_def:
  lookup_env s (i,j) =
    case oEL i s.envs of NONE => NONE | SOME gen_envs => oEL j gen_envs
End

Definition add_decs_generation_def:
  add_decs_generation s =
    case s.env_id_counter of
      (cur_gen,next_id,next_gen) =>
        s with env_id_counter := (next_gen,0,next_gen + 1)
End

Definition add_env_generation_def:
  add_env_generation s =
    s with <|generation := LENGTH s.envs; envs := s.envs ⧺ [[]]|>
End

Definition declare_env_def:
  declare_env es env =
    case es of
    | NONE => NONE
    | SOME (EvalDecs s) =>
      (case s.env_id_counter of
         (cur_gen,next_id,next_gen) =>
           SOME
             (Env env (cur_gen,next_id),
              SOME
                (EvalDecs
                   (s with
                    env_id_counter := (cur_gen,next_id + 1,next_gen)))))
    | SOME (EvalOracle s') =>
      case oEL s'.generation s'.envs of
      | NONE => NONE
      | SOME gen_envs =>
        SOME
          (Conv NONE [nat_to_v s'.generation; nat_to_v (LENGTH gen_envs)],
           SOME
             (EvalOracle
                (s' with
                 envs := LUPDATE (gen_envs ⧺ [env]) s'.generation s'.envs)))
End

(* Concrete, or first-order values, which do not contain code closures and
   are unchanged by many compiler phases. *)
Definition concrete_v_def:
  (concrete_v v ⇔
     case v of
     | Loc _ => T
     | Litv _ => T
     | Conv v_ vs => concrete_v_list vs
     | Vectorv vs => concrete_v_list vs
     | FP_WordTree fp => T
     | FP_BoolTree fp => T
     | Real r => T
     | _ => F) ∧
  (concrete_v_list [] ⇔ T) ∧
  (concrete_v_list (v::vs) ⇔ concrete_v v ∧ concrete_v_list vs)
Termination
  WF_REL_TAC `measure (λx. case x of INL v => v_size v
                                   | INR vs => list_size v_size vs)`
End

Definition compiler_agrees_def:
  compiler_agrees (f:((num#num)#v#(dec)list ->(v#(word8)list#(word64)list)option))
      args (st_v,bs_v,ws_v) ⇔
    case (f args,args,v_to_word8_list bs_v,v_to_word64_list ws_v) of
    | (SOME (st,c_bs,c_ws),(v16,prev_st_v,_),SOME bs,SOME ws) =>
        st = st_v ∧ c_bs = bs ∧ c_ws = ws ∧ concrete_v st_v ∧
        concrete_v prev_st_v
    | _ => F
End

(* get the declarations to be evaluated in the various Eval semantics *)
Definition do_eval_def:
  do_eval vs es =
    case (es,vs) of
    | (SOME (EvalDecs s),[Env env id; st_v; decs_v; st_v2; bs_v; ws_v]) =>
      (case s.decode_decs decs_v of
         NONE => NONE
       | SOME decs =>
         if
           st_v = s.compiler_state ∧ concrete_v decs_v ∧
           compiler_agrees s.compiler (id,st_v,decs) (st_v2,bs_v,ws_v)
         then
           SOME
             (env,decs,
              SOME
                (EvalDecs
                   (add_decs_generation (s with compiler_state := st_v2))))
         else NONE)
    | (SOME (EvalOracle s'),vs) =>
      (case s'.custom_do_eval vs s'.oracle of
         NONE => NONE
       | SOME (env_id,oracle,decs) =>
           case lookup_env s' env_id of
             NONE => NONE
           | SOME env =>
               SOME
               (env,decs,
                SOME
                (EvalOracle (add_env_generation (s' with oracle := oracle)))))
    | _ => NONE
End

(* conclude an Eval generation *)

Definition reset_env_generation_def:
  reset_env_generation prior_es es =
    case (prior_es,es) of
    | (SOME (EvalDecs prior_s'),SOME (EvalDecs s')) =>
      (case (prior_s'.env_id_counter,s'.env_id_counter) of
         ((cur_gen,next_id,v5),v6,v8,next_gen) =>
           SOME
             (EvalDecs
                (s' with env_id_counter := (cur_gen,next_id,next_gen))))
    | (SOME (EvalOracle prior_s),SOME (EvalOracle s)) =>
      SOME (EvalOracle (s with generation := prior_s.generation))
    | _ => es
End

Definition copy_array_def:
  copy_array (src,srcoff) len d =
    if
      srcoff < 0 ∨ len < 0 ∨ LENGTH src < Num (ABS (I (srcoff + len)))
    then
      NONE
    else
      (let
         copied =
           TAKE (Num (ABS (I len))) (DROP (Num (ABS (I srcoff))) src)
       in
         case d of
           NONE => SOME copied
         | SOME (dst,dstoff) =>
           if dstoff < 0 ∨ LENGTH dst < Num (ABS (I (dstoff + len))) then
             NONE
           else
             SOME
               (TAKE (Num (ABS (I dstoff))) dst ⧺ copied ⧺
                DROP (Num (ABS (I (dstoff + len)))) dst))
End

Definition ws_to_chars_def:
  ws_to_chars (ws:word8 list) = MAP (λw. CHR (w2n w)) ws
End

Definition chars_to_ws_def:
  chars_to_ws cs = MAP (λc. i2w (&ORD c)) cs :word8 list
End

Definition opn_lookup_def:
  opn_lookup n =
    case n of
    | Plus => $+
    | Minus => $-
    | Times => $*
    | Divide => $/
    | Modulo => $%
End

Definition opb_lookup_def:
  opb_lookup n =
    case n of Lt => $< | Gt => $> | Leq => $<= | Geq => ($>= : int -> int -> bool)
End

Definition opw8_lookup_def:
  opw8_lookup op =
    case op of
    | Andw => word_and
    | Orw => word_or
    | Xor => word_xor
    | Add => word_add
    | Sub => word_sub : word8 -> word8 -> word8
End

Definition opw64_lookup_def:
  opw64_lookup op =
    case op of
    | Andw => word_and
    | Orw => word_or
    | Xor => word_xor
    | Add => word_add
    | Sub => word_sub : word64 -> word64 -> word64
End

Definition shift8_lookup_def:
  shift8_lookup sh =
    case sh of
    |  Lsl => word_lsl
    | Lsr => word_lsr
    | Asr => word_asr
    | Ror => word_ror : word8 -> num -> word8
End

Definition shift64_lookup_def:
  shift64_lookup sh =
    case sh of
    | Lsl => word_lsl
    | Lsr => word_lsr
    | Asr => word_asr
    | Ror => word_ror : word64 -> num -> word64
End

Datatype:
  exp_or_val = Exp exp | Val v
End

Type store_ffi = “: 'v store # 'ffi ffi_state”

Definition do_fprw_def:
 do_fprw (v:(v,v) result) fp_opt fp_rws=
   (case (v, fp_opt) of
    (Rval (FP_BoolTree fv), rws) =>
    (case rwAllBoolTree rws fp_rws fv of
      NONE => NONE
    | SOME fv_opt => SOME (Rval (FP_BoolTree fv_opt))
    )
  | (Rval (FP_WordTree fv), rws) =>
    (case rwAllWordTree rws fp_rws fv of
      NONE => NONE
    | SOME fv_opt => SOME (Rval (FP_WordTree fv_opt))
    )
  | (Rval r, [] ) => SOME v
  | (_, _) => NONE)
End

Definition do_fpoptimise_def:
 do_fpoptimise sc [] = [] ∧
 do_fpoptimise sc [Litv l] = [Litv l] ∧
 do_fpoptimise sc [Conv st vs] = [Conv st (do_fpoptimise sc vs)] ∧
 do_fpoptimise sc [Closure env x e] = [Closure env x e] ∧
 do_fpoptimise sc [Recclosure env ls x] = [Recclosure env ls x] ∧
 do_fpoptimise sc [Loc n] = [Loc n] ∧
 do_fpoptimise sc [Vectorv vs] = [Vectorv (do_fpoptimise sc vs)] ∧
 do_fpoptimise sc [Real r]=  [Real r]  ∧
 do_fpoptimise sc [FP_WordTree fp] = [FP_WordTree (Fp_wopt sc fp)] ∧
 do_fpoptimise sc [FP_BoolTree fp] = [FP_BoolTree (Fp_bopt sc fp)] ∧
 do_fpoptimise sc [Env env n] = [Env env n] ∧
 do_fpoptimise sc (v::vs) = (do_fpoptimise sc [v]) ++ (do_fpoptimise sc vs)
Termination
  WF_REL_TAC `measure (\ (_, l). v1_size l)` \\ fs[]
End

Definition do_app_def:
  do_app (s: v store_v list, t: 'ffi ffi_state) op vs =
    case (op, vs) of
      (ListAppend, [x1; x2]) =>
      (case (v_to_list x1, v_to_list x2) of
          (SOME xs, SOME ys) => SOME ((s,t), Rval (list_to_v (xs ++ ys)))
        | _ => NONE
      )
    | (Opn op, [Litv (IntLit n1); Litv (IntLit n2)]) =>
        if ((op = Divide) \/ (op = Modulo)) /\ (n2 =( 0 : int)) then
          SOME ((s,t), Rerr (Rraise div_exn_v))
        else
          SOME ((s,t), Rval (Litv (IntLit (opn_lookup op n1 n2))))
    | (Opb op, [Litv (IntLit n1); Litv (IntLit n2)]) =>
        SOME ((s,t), Rval (Boolv (opb_lookup op n1 n2)))
    | (Opw W8 op, [Litv (Word8 w1); Litv (Word8 w2)]) =>
        SOME ((s,t), Rval (Litv (Word8 (opw8_lookup op w1 w2))))
    | (Opw W64 op, [Litv (Word64 w1); Litv (Word64 w2)]) =>
        SOME ((s,t), Rval (Litv (Word64 (opw64_lookup op w1 w2))))
    | (Opw W64 op, [FP_WordTree w1; Litv (Word64 w2)]) =>
        let wr1 = (compress_word w1) in
          SOME ((s,t), Rval (Litv (Word64 (opw64_lookup op wr1 w2))))
    | (Opw W64 op, [Litv (Word64 w1); FP_WordTree w2]) =>
        let wr2 = (compress_word w2) in
          SOME ((s,t), Rval (Litv (Word64 (opw64_lookup op w1 wr2))))
    | (Opw W64 op, [FP_WordTree w1; FP_WordTree w2]) =>
        let wr1 = (compress_word w1) in
        let wr2 = (compress_word w2) in
          SOME ((s,t), Rval (Litv (Word64 (opw64_lookup op wr1 wr2))))
    | (FP_top t_op, [v1; v2; v3]) =>
        (case (fp_translate v1, fp_translate v2, fp_translate v3) of
          (SOME (FP_WordTree w1), SOME (FP_WordTree w2), SOME (FP_WordTree w3)) =>
          SOME ((s,t), Rval (FP_WordTree (fp_top t_op w1 w2 w3)))
        | _ => NONE
        )
    | (FP_bop bop, [v1; v2]) =>
        (case (fp_translate v1, fp_translate v2) of
          (SOME (FP_WordTree w1), SOME (FP_WordTree w2)) =>
          SOME ((s,t),Rval (FP_WordTree (fp_bop bop w1 w2)))
        | _ => NONE
        )
    | (FP_uop uop, [v1]) =>
        (case (fp_translate v1) of
          (SOME (FP_WordTree w1)) =>
          SOME ((s,t),Rval (FP_WordTree (fp_uop uop w1)))
        | _ => NONE
        )
    | (FP_cmp cmp, [v1; v2]) =>
        (case (fp_translate v1, fp_translate v2) of
          (SOME (FP_WordTree w1), SOME (FP_WordTree w2)) =>
          SOME ((s,t),Rval (FP_BoolTree (fp_cmp cmp w1 w2)))
        | _ => NONE
        )
    | (FpToWord, [FP_WordTree v1]) => SOME ((s,t), Rval (Litv (Word64 (compress_word v1))))
    | (FpFromWord, [Litv (Word64 v1)]) => (SOME ((s,t), Rval (FP_WordTree (Fp_const v1))))
    | (Real_cmp cmp, [Real v1; Real v2]) =>
        SOME ((s,t), Rval (Boolv (real_cmp cmp v1 v2)))
    | (Real_bop bop, [Real v1; Real v2]) =>
        SOME ((s,t), Rval (Real (real_bop bop v1 v2)))
    | (Real_uop uop, [Real v1]) =>
        SOME ((s,t), Rval (Real (real_uop uop v1)))
    | (RealFromFP, [Litv (Word64 fp)]) =>
        SOME ((s,t), Rval (Real (fp64_to_real fp)))
    | (Shift W8 op n, [Litv (Word8 w)]) =>
        SOME ((s,t), Rval (Litv (Word8 (shift8_lookup op w n))))
    | (Shift W64 op n, [Litv (Word64 w)]) =>
        SOME ((s,t), Rval (Litv (Word64 (shift64_lookup op w n))))
    | (Shift W64 op n, [FP_WordTree w1]) =>
        let wr1 = (compress_word w1) in
          (SOME ((s,t), Rval (Litv (Word64 (shift64_lookup op wr1 n)))))
    | (Equality, [v1; v2]) =>
        (case do_eq v1 v2 of
            Eq_type_error => NONE
          | Eq_val b => SOME ((s,t), Rval (Boolv b))
        )
    | (Opassign, [Loc lnum; v]) =>
        (case store_assign lnum (Refv v) s of
            SOME s' => SOME ((s',t), Rval (Conv NONE []))
          | NONE => NONE
        )
    | (Opref, [v]) =>
        let (s',n) = (store_alloc (Refv v) s) in
          SOME ((s',t), Rval (Loc n))
    | (Opderef, [Loc n]) =>
        (case store_lookup n s of
            SOME (Refv v) => SOME ((s,t),Rval v)
          | _ => NONE
        )
    | (Aw8alloc, [Litv (IntLit n); Litv (Word8 w)]) =>
        if n <( 0 : int) then
          SOME ((s,t), Rerr (Rraise sub_exn_v))
        else
          let (s',lnum) =
            (store_alloc (W8array (REPLICATE (Num (ABS (I n))) w)) s)
          in
            SOME ((s',t), Rval (Loc lnum))
    | (Aw8sub, [Loc lnum; Litv (IntLit i)]) =>
        (case store_lookup lnum s of
            SOME (W8array ws) =>
              if i <( 0 : int) then
                SOME ((s,t), Rerr (Rraise sub_exn_v))
              else
                let n = (Num (ABS (I i))) in
                  if n >= LENGTH ws then
                    SOME ((s,t), Rerr (Rraise sub_exn_v))
                  else
                    SOME ((s,t), Rval (Litv (Word8 (EL n ws))))
          | _ => NONE
        )
    | (Aw8sub_unsafe, [Loc lnum; Litv (IntLit i)]) =>
        (case store_lookup lnum s of
            SOME (W8array ws) =>
              if i <( 0 : int) then
                NONE
              else
                let n = (Num (ABS (I i))) in
                  if n >= LENGTH ws then
                    NONE
                  else
                    SOME ((s,t), Rval (Litv (Word8 (EL n ws))))
          | _ => NONE
        )
    | (Aw8length, [Loc n]) =>
        (case store_lookup n s of
            SOME (W8array ws) =>
              SOME ((s,t),Rval (Litv(IntLit(int_of_num(LENGTH ws)))))
          | _ => NONE
         )
    | (Aw8update, [Loc lnum; Litv(IntLit i); Litv(Word8 w)]) =>
        (case store_lookup lnum s of
          SOME (W8array ws) =>
            if i <( 0 : int) then
              SOME ((s,t), Rerr (Rraise sub_exn_v))
            else
              let n = (Num (ABS (I i))) in
                if n >= LENGTH ws then
                  SOME ((s,t), Rerr (Rraise sub_exn_v))
                else
                  (case store_assign lnum (W8array (LUPDATE w n ws)) s of
                      NONE => NONE
                    | SOME s' => SOME ((s',t), Rval (Conv NONE []))
                  )
        | _ => NONE
      )
    | (Aw8update_unsafe, [Loc lnum; Litv(IntLit i); Litv(Word8 w)]) =>
        (case store_lookup lnum s of
          SOME (W8array ws) =>
            if i <( 0 : int) then
              NONE
            else
              let n = (Num (ABS (I i))) in
                if n >= LENGTH ws then
                  NONE
                else
                  (case store_assign lnum (W8array (LUPDATE w n ws)) s of
                      NONE => NONE
                    | SOME s' => SOME ((s',t), Rval (Conv NONE []))
                  )
        | _ => NONE
      )
    | (WordFromInt W8, [Litv(IntLit i)]) =>
        SOME ((s,t), Rval (Litv (Word8 (i2w i))))
    | (WordFromInt W64, [Litv(IntLit i)]) =>
        SOME ((s,t), Rval (Litv (Word64 (i2w i))))
    | (WordToInt W8, [Litv (Word8 w)]) =>
        SOME ((s,t), Rval (Litv (IntLit (int_of_num(w2n w)))))
    | (WordToInt W64, [Litv (Word64 w)]) =>
        SOME ((s,t), Rval (Litv (IntLit (int_of_num(w2n w)))))
    | (WordToInt W64, [FP_WordTree v]) =>
        let w = (compress_word v) in
          SOME ((s,t), Rval (Litv (IntLit (int_of_num(w2n w)))))
    | (CopyStrStr, [Litv(StrLit str);Litv(IntLit off);Litv(IntLit len)]) =>
        SOME ((s,t),
        (case copy_array (EXPLODE str,off) len NONE of
          NONE => Rerr (Rraise sub_exn_v)
        | SOME cs => Rval (Litv(StrLit(IMPLODE(cs))))
        ))
    | (CopyStrAw8, [Litv(StrLit str);Litv(IntLit off);Litv(IntLit len);
                    Loc dst;Litv(IntLit dstoff)]) =>
        (case store_lookup dst s of
          SOME (W8array ws) =>
            (case copy_array (EXPLODE str,off) len (SOME(ws_to_chars ws,dstoff)) of
              NONE => SOME ((s,t), Rerr (Rraise sub_exn_v))
            | SOME cs =>
              (case store_assign dst (W8array (chars_to_ws cs)) s of
                SOME s' =>  SOME ((s',t), Rval (Conv NONE []))
              | _ => NONE
              )
            )
        | _ => NONE
        )
    | (CopyAw8Str, [Loc src;Litv(IntLit off);Litv(IntLit len)]) =>
      (case store_lookup src s of
        SOME (W8array ws) =>
        SOME ((s,t),
          (case copy_array (ws,off) len NONE of
            NONE => Rerr (Rraise sub_exn_v)
          | SOME ws => Rval (Litv(StrLit(IMPLODE(ws_to_chars ws))))
          ))
      | _ => NONE
      )
    | (CopyAw8Aw8, [Loc src;Litv(IntLit off);Litv(IntLit len);
                    Loc dst;Litv(IntLit dstoff)]) =>
      (case (store_lookup src s, store_lookup dst s) of
        (SOME (W8array ws), SOME (W8array ds)) =>
          (case copy_array (ws,off) len (SOME(ds,dstoff)) of
            NONE => SOME ((s,t), Rerr (Rraise sub_exn_v))
          | SOME ws =>
              (case store_assign dst (W8array ws) s of
                SOME s' => SOME ((s',t), Rval (Conv NONE []))
              | _ => NONE
              )
          )
      | _ => NONE
      )
    | (Ord, [Litv (Char c)]) =>
          SOME ((s,t), Rval (Litv(IntLit(int_of_num(ORD c)))))
    | (Chr, [Litv (IntLit i)]) =>
        SOME ((s,t),
          (if (i <( 0 : int)) \/ (i >( 255 : int)) then
            Rerr (Rraise chr_exn_v)
          else
            Rval (Litv(Char(CHR(Num (ABS (I i))))))))
    | (Chopb op, [Litv (Char c1); Litv (Char c2)]) =>
        SOME ((s,t), Rval (Boolv (opb_lookup op (int_of_num(ORD c1)) (int_of_num(ORD c2)))))
    | (Implode, [v]) =>
          (case v_to_char_list v of
            SOME ls =>
              SOME ((s,t), Rval (Litv (StrLit (IMPLODE ls))))
          | NONE => NONE
          )
    | (Explode, [v]) =>
          (case v of
            Litv (StrLit str) =>
              SOME ((s,t), Rval (list_to_v (MAP (\ c .  Litv (Char c)) (EXPLODE str))))
          | _ => NONE
          )
    | (Strsub, [Litv (StrLit str); Litv (IntLit i)]) =>
        if i <( 0 : int) then
          SOME ((s,t), Rerr (Rraise sub_exn_v))
        else
          let n = (Num (ABS (I i))) in
            if n >= STRLEN str then
              SOME ((s,t), Rerr (Rraise sub_exn_v))
            else
              SOME ((s,t), Rval (Litv (Char (EL n (EXPLODE str)))))
    | (Strlen, [Litv (StrLit str)]) =>
        SOME ((s,t), Rval (Litv(IntLit(int_of_num(STRLEN str)))))
    | (Strcat, [v]) =>
        (case v_to_list v of
          SOME vs =>
            (case vs_to_string vs of
              SOME str =>
                SOME ((s,t), Rval (Litv(StrLit str)))
            | _ => NONE
            )
        | _ => NONE
        )
    | (VfromList, [v]) =>
          (case v_to_list v of
              SOME vs =>
                SOME ((s,t), Rval (Vectorv vs))
            | NONE => NONE
          )
    | (Vsub, [Vectorv vs; Litv (IntLit i)]) =>
        if i <( 0 : int) then
          SOME ((s,t), Rerr (Rraise sub_exn_v))
        else
          let n = (Num (ABS (I i))) in
            if n >= LENGTH vs then
              SOME ((s,t), Rerr (Rraise sub_exn_v))
            else
              SOME ((s,t), Rval (EL n vs))
    | (Vlength, [Vectorv vs]) =>
        SOME ((s,t), Rval (Litv (IntLit (int_of_num (LENGTH vs)))))
    | (Aalloc, [Litv (IntLit n); v]) =>
        if n <( 0 : int) then
          SOME ((s,t), Rerr (Rraise sub_exn_v))
        else
          let (s',lnum) =
            (store_alloc (Varray (REPLICATE (Num (ABS (I n))) v)) s)
          in
            SOME ((s',t), Rval (Loc lnum))
    | (AallocEmpty, [Conv NONE []]) =>
        let (s',lnum) = (store_alloc (Varray []) s) in
          SOME ((s',t), Rval (Loc lnum))
    | (AallocFixed, vs) =>
        let (s',lnum) =
          (store_alloc (Varray vs) s)
        in
          SOME ((s',t), Rval (Loc lnum))
    | (Asub, [Loc lnum; Litv (IntLit i)]) =>
        (case store_lookup lnum s of
            SOME (Varray vs) =>
              if i <( 0 : int) then
                SOME ((s,t), Rerr (Rraise sub_exn_v))
              else
                let n = (Num (ABS (I i))) in
                  if n >= LENGTH vs then
                    SOME ((s,t), Rerr (Rraise sub_exn_v))
                  else
                    SOME ((s,t), Rval (EL n vs))
          | _ => NONE
        )
    | (Asub_unsafe, [Loc lnum; Litv (IntLit i)]) =>
        (case store_lookup lnum s of
            SOME (Varray vs) =>
              if i <( 0 : int) then
                NONE
              else
                let n = (Num (ABS (I i))) in
                  if n >= LENGTH vs then
                    NONE
                  else
                    SOME ((s,t), Rval (EL n vs))
          | _ => NONE
        )
    | (Alength, [Loc n]) =>
        (case store_lookup n s of
            SOME (Varray ws) =>
              SOME ((s,t),Rval (Litv(IntLit(int_of_num(LENGTH ws)))))
          | _ => NONE
         )
    | (Aupdate, [Loc lnum; Litv (IntLit i); v]) =>
        (case store_lookup lnum s of
          SOME (Varray vs) =>
            if i <( 0 : int) then
              SOME ((s,t), Rerr (Rraise sub_exn_v))
            else
              let n = (Num (ABS (I i))) in
                if n >= LENGTH vs then
                  SOME ((s,t), Rerr (Rraise sub_exn_v))
                else
                  (case store_assign lnum (Varray (LUPDATE v n vs)) s of
                      NONE => NONE
                    | SOME s' => SOME ((s',t), Rval (Conv NONE []))
                  )
        | _ => NONE
      )
    | (Aupdate_unsafe, [Loc lnum; Litv (IntLit i); v]) =>
        (case store_lookup lnum s of
          SOME (Varray vs) =>
            if i <( 0 : int) then
              NONE
            else
              let n = (Num (ABS (I i))) in
                if n >= LENGTH vs then
                  NONE
                else
                  (case store_assign lnum (Varray (LUPDATE v n vs)) s of
                      NONE => NONE
                    | SOME s' => SOME ((s',t), Rval (Conv NONE []))
                  )
        | _ => NONE
      )
    | (ConfigGC, [Litv (IntLit i); Litv (IntLit j)]) =>
        SOME ((s,t), Rval (Conv NONE []))
    | (FFI n, [Litv(StrLit conf); Loc lnum]) =>
        (case store_lookup lnum s of
          SOME (W8array ws) =>
            (case call_FFI t n (MAP (\ c .  n2w(ORD c)) (EXPLODE conf)) ws of
              FFI_return t' ws' =>
               (case store_assign lnum (W8array ws') s of
                 SOME s' => SOME ((s', t'), Rval (Conv NONE []))
               | NONE => NONE
               )
            | FFI_final outcome =>
               SOME ((s, t), Rerr (Rabort (Rffi_error outcome)))
            )
        | _ => NONE
        )
    | (Env_id, [Env env (gen, id)]) => SOME ((s, t),
            Rval (Conv NONE [nat_to_v gen; nat_to_v id]))
    | (Env_id, [Conv NONE [gen; id]]) => SOME ((s, t),
            Rval (Conv NONE [gen; id]))
    | _ => NONE
End

(* Do a logical operation *)
Definition do_log_def:
  do_log l v e =
    if l = And ∧ v = Boolv T ∨ l = Or ∧ v = Boolv F then SOME (Exp e)
    else if l = And ∧ v = Boolv F ∨ l = Or ∧ v = Boolv T then SOME (Val v)
    else NONE
End

(* Do an if-then-else *)
Definition do_if_def:
  do_if v e1 e2 =
    if v = Boolv T then SOME e1 else if v = Boolv F then SOME e2 else NONE
End

(* Semantic helpers for definitions *)

Definition build_constrs_def:
  build_constrs stamp condefs =
    MAP (λ(conN,ts). (conN,LENGTH ts,TypeStamp conN stamp)) condefs
End

(* Build a constructor environment for the type definition tds *)
Definition build_tdefs_def:
  build_tdefs next_stamp ([]:((tvarN)list#string#(string#(ast_t)list)list)list) =
    ((alist_to_ns []):((string),(string),(num#stamp))namespace) ∧
  build_tdefs next_stamp ((tvs,tn,condefs)::tds) =
    nsAppend (build_tdefs (next_stamp + 1) tds)
      (alist_to_ns (REVERSE (build_constrs next_stamp condefs)))
End

(* Checks that no constructor is defined twice in a type *)
Definition check_dup_ctors_def:
  check_dup_ctors ((tvs,tn,condefs):(tvarN)list#string#(string#(ast_t)list)list) ⇔
    ALL_DISTINCT
      (let x2 = [] in
         FOLDR (λ(n,ts) x2. if T then n::x2 else x2) x2 condefs)
End

Definition combine_dec_result_def:
  combine_dec_result env (r:((v sem_env),'a)result) =
    case r of
    | Rval env' => Rval <|v := nsAppend env'.v env.v; c := nsAppend env'.c env.c|>
    | Rerr e => Rerr e
End

Definition extend_dec_env_def:
  extend_dec_env new_env (env: v sem_env) =
    <|c := nsAppend new_env.c env.c; v := nsAppend new_env.v env.v|>
End

Definition shift_fp_opts_def:
  shift_fp_opts s =
  (s with <| fp_state :=
             s.fp_state with <|
                opts := (\ x . s.fp_state.opts (x + 1));
                choices := (s.fp_state.choices + 1)
             |>
          |>)
End

val _ = set_fixity "+++" (Infixl 480);
Overload "+++" = “extend_dec_env”;

val _ = export_theory()
