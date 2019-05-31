(*
  Various ML tools for dealing with the asm language.
*)
structure asmLib :> asmLib =
struct

open HolKernel boolLib bossLib
open asmTheory asmSemTheory asmPropsTheory utilsLib

structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars asmPropsTheory.asmProps_grammars
end

open Parse


val ERR = Feedback.mk_HOL_ERR "asmLib"

(* some rewrites ---------------------------------------------------------- *)

fun read_mem_word n =
   EVAL ``(read_mem_word (b: 'a word) ^n s): 'a word # 'a asm_state``
   |> SIMP_RULE (srw_ss()) []

fun write_mem_word n =
   EVAL ``(write_mem_word (b: 'a word) ^n (d:'b word) s): 'a asm_state``
   |> SIMP_RULE (srw_ss()) []

val asm_ok_rwts =
   [asm_ok_def, inst_ok_def, reg_ok_def, fp_reg_ok_def, arith_ok_def, fp_ok_def,
    cmp_ok_def, reg_imm_ok_def, offset_ok_def, alignmentTheory.aligned_0]

val asm_rwts =
   [upd_pc_def, upd_reg_def, upd_fp_reg_def, upd_mem_def, read_reg_def,
    read_fp_reg_def, read_mem_def, assert_def, reg_imm_def, binop_upd_def,
    word_cmp_def, word_shift_def, arith_upd_def, fp_upd_def, addr_def,
    mem_load_def, write_mem_word_def, mem_store_def,
    read_mem_word ``1n``, read_mem_word ``4n``, read_mem_word ``8n``,
    write_mem_word ``1n``, write_mem_word ``4n``, write_mem_word ``8n``,
    mem_op_def, inst_def, jump_to_offset_def, asm_def,
    prove
      (“!a b x:'a y. a /\ (a ==> ~b) ==> ((if b then x else y) = y)”, rw [])
    ]

(* compset support -------------------------------------------------------- *)

val (asm_ok_tm, mk_asm_ok, dest_asm_ok, is_asm_ok) =
  HolKernel.syntax_fns2 "asm" "asm_ok"

local
  val accessors =
    List.map
      (fst o Term.dest_comb o boolSyntax.lhs o Thm.concl o Drule.SPEC_ALL)
      (TypeBase.accessors_of ``:'a asm_config``)
  fun asm_config_rwts tc =
    utilsLib.map_conv EVAL
      (List.map (fn f => boolSyntax.mk_icomb (f, tc)) accessors)
  val asm_tms =
    [
     `Inst Skip : 'a asm`,
     `Inst (Const r w) : 'a asm`,
     `Inst (Arith (Binop b r1 r2 (Reg r3))) : 'a asm`,
     `Inst (Arith (Binop b r1 r2 (Imm w))) : 'a asm`,
     `Inst (Arith (Shift s r1 r2 n)) : 'a asm`,
     `Inst (Arith (Div r1 r2 r3)) : 'a asm`,
     `Inst (Arith (LongMul r1 r2 r3 r4)) : 'a asm`,
     `Inst (Arith (LongDiv r1 r2 r3 r4 r5)) : 'a asm`,
     `Inst (Arith (AddCarry r1 r2 r3 r4)) : 'a asm`,
     `Inst (Arith (AddOverflow r1 r2 r3 r4)) : 'a asm`,
     `Inst (Arith (SubOverflow r1 r2 r3 r4)) : 'a asm`,
     `Inst (Mem Load r1 (Addr r2 w)) : 'a asm`,
     `Inst (Mem Load8 r1 (Addr r2 w)) : 'a asm`,
     `Inst (Mem Load32 r1 (Addr r2 w)) : 'a asm`,
     `Inst (Mem Store r1 (Addr r2 w)) : 'a asm`,
     `Inst (Mem Store8 r1 (Addr r2 w)) : 'a asm`,
     `Inst (Mem Store32 r1 (Addr r2 w)) : 'a asm`,
     `Inst (FP (FPLess r d1 d2)) : 'a asm`,
     `Inst (FP (FPLessEqual r d1 d2)) : 'a asm`,
     `Inst (FP (FPEqual r d1 d2)) : 'a asm`,
     `Inst (FP (FPMov d1 d2)) : 'a asm`,
     `Inst (FP (FPMovToReg r1 r2 d)) : 'a asm`,
     `Inst (FP (FPMovFromReg d r1 r2)) : 'a asm`,
     `Inst (FP (FPToInt r d)) : 'a asm`,
     `Inst (FP (FPFromInt d r)) : 'a asm`,
     `Inst (FP (FPAbs d1 d2)) : 'a asm`,
     `Inst (FP (FPNeg d1 d2)) : 'a asm`,
     `Inst (FP (FPSqrt d1 d2)) : 'a asm`,
     `Inst (FP (FPAdd d1 d2 d3)) : 'a asm`,
     `Inst (FP (FPSub d1 d2 d3)) : 'a asm`,
     `Inst (FP (FPMul d1 d2 d3)) : 'a asm`,
     `Inst (FP (FPDiv d1 d2 d3)) : 'a asm`,
     `Inst (FP (FPFma d1 d2 d3)) : 'a asm`,
     `Jump w : 'a asm`,
     `JumpCmp x r1 (Reg r2) w : 'a asm`,
     `JumpCmp x r1 (Imm i) w : 'a asm`,
     `Call r : 'a asm`,
     `JumpReg r : 'a asm`,
     `Loc r w : 'a asm`
    ]
  val conv = SIMP_CONV (srw_ss()++boolSimps.CONJ_ss++boolSimps.LET_ss)
in
  fun target_asm_rwts rwts tc =
    let
      val ty = hd (snd (Type.dest_type (Term.type_of tc)))
      val parse_term = Term.inst [Type.alpha |-> ty] o Parse.Term
      val w = Term.mk_var ("a", wordsSyntax.mk_word_type ty)
      val rwt = asm_config_rwts tc
    in
      (rwt,
       utilsLib.map_conv (conv (rwt :: rwts @ asm_ok_rwts))
         (List.map (fn i => mk_asm_ok (parse_term i, tc)) asm_tms))
    end
end

local
  val aligned2 =
    Conv.RIGHT_CONV_RULE EVAL
      (SPECL [“2n”, “x:α words$word”] alignmentTheory.aligned_bitwise_and)
  val rwts = ref ([aligned2] : thm list)
  val cnv = ref NO_CONV
  val pair_term_compare = Lib.pair_compare (Term.compare, Term.compare)
in
  fun add_asm_ok_thm th =
    ( rwts := th :: !rwts
    ; cnv := (PURE_REWRITE_CONV (!rwts) THENC wordsLib.WORD_EVAL_CONV)
    )
  val asm_ok_conv =
    Conv.memoize (Lib.total dest_asm_ok) (Redblackmap.mkDict pair_term_compare)
      (not o is_asm_ok) (ERR "asm_ok_conv" "") (fn t => !cnv t)
end

fun ast_type a s = Type.mk_thy_type {Thy = "ast", Tyop = s, Args = a}
val ast_type0 = ast_type []

fun asm_type a s = Type.mk_thy_type {Thy = "asm", Tyop = s, Args = a}
val asm_type0 = asm_type []
val asm_type = asm_type [``:64``]

val add_asm_compset = computeLib.extend_compset
  [computeLib.Defs
     [upd_pc_def, upd_reg_def, upd_fp_reg_def, upd_mem_def, read_reg_def,
      read_fp_reg_def, read_mem_def, assert_def, reg_imm_def, binop_upd_def,
      word_cmp_def, word_shift_def, arith_upd_def, fp_upd_def, addr_def,
      mem_load_def, write_mem_word_def, mem_store_def, read_mem_word_def,
      mem_op_def, is_test_def, inst_def, jump_to_offset_def,
      asm_def, alignmentTheory.aligned_extract,offset_ok_def],
   computeLib.Convs
     [(asm_ok_tm, 2, asm_ok_conv)],
   computeLib.Tys
     (List.map ast_type0 ["shift"] @
      List.map asm_type0 ["cmp", "memop", "binop", "fp"] @
      List.map asm_type  ["asm_config", "asm", "inst", "arith"])]

(* some custom tools/tactics ---------------------------------------------- *)

fun print_tac s1 s2 gs =
  (print (s2 ^ (if s1 = "" then "" else " (" ^ s1 ^ ")") ^ "\n"); ALL_TAC gs)

fun using_first n thms_tac =
   POP_ASSUM_LIST
      (fn thms =>
          let
             val x = List.rev (List.take (thms, n))
             val y = List.rev (List.drop (thms, n))
          in
             MAP_EVERY assume_tac y
             \\ thms_tac x
             \\ MAP_EVERY assume_tac x
          end)

val (_, mk_bytes_in_memory, dest_bytes_in_memory, _) =
   HolKernel.syntax_fns4 "misc" "bytes_in_memory"

val strip_bytes_in_memory =
   Option.map (fn (_, l, _, _) => fst (listSyntax.dest_list l)) o
   Lib.total dest_bytes_in_memory

local
   val bytes_in_memory_concat =
      GENL [“l1: word8 list”, “l2 : word8 list”]
         (fst (Thm.EQ_IMP_RULE (Drule.SPEC_ALL miscTheory.bytes_in_memory_APPEND)))
   val w8 = ``:word8``
   val pc = Term.mk_var ("pc", ``:'a word``)
   val mem = Term.mk_var ("mem", ``: 'a word -> word8``)
   val mem_domain = Term.mk_var ("mem_domain", ``: 'a word -> bool``)
in
   fun split_bytes_in_memory_tac n (asl, g) =
      (case List.mapPartial strip_bytes_in_memory asl of
          [] => NO_TAC
        | l :: _ =>
            let
               val _ = n <= List.length l orelse
                       raise ERR "split_bytes_in_memory_tac" "too few bytes"
               val l1 = listSyntax.mk_list (List.take (l, n), w8)
               val l2 = listSyntax.mk_list (List.drop (l, n), w8)
               val l = listSyntax.mk_list (l, w8)
               val th =
                  bytes_in_memory_concat
                  |> Drule.ISPECL [l1, l2]
                  |> Conv.CONV_RULE
                       (Conv.PATH_CONV "lrllr" listLib.APPEND_CONV
                        THENC Conv.PATH_CONV "rrlllr"
                                (Conv.DEPTH_CONV listLib.LENGTH_CONV))
            in
               qpat_x_assum `misc$bytes_in_memory ^pc ^l ^mem ^mem_domain`
                  (fn thm =>
                      let
                         val (th1, th2) =
                            Drule.CONJ_PAIR (Drule.MATCH_MP th thm)
                      in
                         assume_tac th1
                         \\ assume_tac th2
                      end)
            end) (asl, g)
end

local
   fun bit_mod_thm n m =
      let
         val M = Parse.Term m
         val N = Parse.Term n
         val th = bitTheory.BITS_ZERO3 |> SPEC N |> numLib.REDUCE_RULE
      in
         Tactical.prove (
             ``BIT ^M n = BIT ^M (n MOD 2 ** (^N + 1))``,
             simp [bitTheory.BIT_def, GSYM th, bitTheory.BITS_COMP_THM2])
         |> numLib.REDUCE_RULE
      end
   fun nq i = [QUOTE (Int.toString i ^ "n")]
   val th = GSYM wordsTheory.n2w_mod
   fun bit_mod_thms n =
      (th |> Thm.INST_TYPE [Type.alpha |-> fcpSyntax.mk_int_numeric_type n]
          |> CONV_RULE (DEPTH_CONV wordsLib.SIZES_CONV)) ::
      List.tabulate (n, fn j => bit_mod_thm (nq (n - 1)) (nq j))
in
   fun v2w_BIT_n2w i =
      let
         val n = Term.mk_var ("n", numLib.num)
         val ty = fcpSyntax.mk_int_numeric_type i
         val r = wordsSyntax.mk_n2w (n, ty)
         val l = List.tabulate
                    (i, fn j => bitSyntax.mk_bit (numSyntax.term_of_int j, n))
         val v = bitstringSyntax.mk_v2w
                    (listSyntax.mk_list (List.rev l, Type.bool), ty)
         val s =
            numSyntax.mk_numeral (Arbnum.pow (Arbnum.two, Arbnum.fromInt i))
      in
         Tactical.prove(boolSyntax.mk_eq (v, r),
            once_rewrite_tac (bit_mod_thms i)
            \\ qabbrev_tac `m = n MOD ^s`
            \\ `m < ^s` by simp [Abbr `m`]
            \\ full_simp_tac std_ss [wordsTheory.NUMERAL_LESS_THM]
            \\ EVAL_TAC
            ) |> GEN_ALL
      end
end

local
   fun is_byte_eq tm =
      let
        val (l, r) = boolSyntax.dest_eq tm
      in
        (wordsSyntax.is_word_extract l orelse wordsSyntax.is_word_concat l)
        andalso (bitstringSyntax.is_v2w r orelse wordsSyntax.is_n2w r)
      end
   val conv =
      Conv.DEPTH_CONV
         (fn tm => if is_byte_eq tm
                      then blastLib.BBLAST_CONV tm
                   else Conv.NO_CONV tm)
      THENC Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV
in
   val byte_eq_tac =
      rule_assum_tac
        (Conv.CONV_RULE
           (fn tm =>
               if boolSyntax.is_imp_only tm orelse boolSyntax.is_forall tm
                  then conv tm
               else ALL_CONV tm))
end

local
  fun get tm =
    Option.getOpt
      (Lib.total lhs tm,
       if boolSyntax.is_neg tm then boolSyntax.F else boolSyntax.T)
in
  fun mk_blast_thm l =
    let
      val lty = Term.type_of l
      val ty = wordsSyntax.dest_word_type lty
      val r =
        blastLib.BBLAST_CONV (boolSyntax.mk_eq (l, Term.mk_var ("_", lty)))
        |> concl |> rhs |> strip_conj |> List.map get |> List.rev
        |> (fn l => listSyntax.mk_list (l, Type.bool))
        |> (fn tm => bitstringSyntax.mk_v2w (tm, ty))
    in
      blastLib.BBLAST_PROVE (boolSyntax.mk_eq (r, l)) |> SIMP_RULE bool_ss []
    end
end

local
   fun dest_env P tm =
      case Lib.total boolSyntax.strip_comb tm of
         SOME (env, [n, ms]) =>
            if Lib.total (fst o Term.dest_var) env = SOME "env" andalso
               not (P ms) andalso numSyntax.is_numeral n
               then (n, ms)
            else raise ERR "dest_env" ""
       | _ => raise ERR "dest_env" ""
   val find_the_env =
     let
       val dest_env = dest_env optionSyntax.is_the
       val is_env = Lib.can dest_env
     in
       HolKernel.bvk_find_term (is_env o snd) dest_env
     end
in
   fun find_env P g =
      g |> boolSyntax.strip_conj |> List.last
        |> HolKernel.find_terms (Lib.can (dest_env P))
        |> Lib.op_mk_set aconv
        |> mlibUseful.sort_map (HolKernel.term_size) Int.compare
        |> Lib.total (dest_env P o List.last)
   fun env_tac f (asl, g) =
      (case find_the_env g of
          SOME t_tm =>
            let
               val (tm2, tac) = f t_tm
            in
               Tactical.SUBGOAL_THEN tm2 (fn th => once_rewrite_tac [th])
               >| [tac, all_tac]
            end
        | NONE => ALL_TAC) (asl, g)
end

fun asm_cases_tac i =
  Cases_on i
  >| [
    Q.MATCH_GOALSUB_RENAME_TAC `Inst i`
    \\ Cases_on `i`
    >| [
      all_tac, (* Skip *)
      all_tac, (* Concst *)
      Q.MATCH_GOALSUB_RENAME_TAC `Arith a`
      \\ Cases_on `a`
      >| [
        Q.MATCH_GOALSUB_RENAME_TAC `Binop b _ _ r`
        \\ Cases_on `r`
        \\ Cases_on `b`,
        Q.MATCH_GOALSUB_RENAME_TAC `Shift s _ _ _`
        \\ Cases_on `s`,
        all_tac, (* Div *)
        all_tac, (* LongMul *)
        all_tac, (* LongDiv *)
        all_tac, (* AddCarry *)
        all_tac, (* AddOverflow *)
        all_tac  (* SubOverflow *)
      ],
      Q.MATCH_GOALSUB_RENAME_TAC `Mem m _ a`
      \\ Cases_on `a`
      \\ Cases_on `m`,
      Q.MATCH_GOALSUB_RENAME_TAC `FP a`
      \\ Cases_on `a`
    ],
    all_tac, (* Jump *)
    Q.MATCH_GOALSUB_RENAME_TAC `JumpCmp c _ r _`
    \\ Cases_on `r`
    \\ Cases_on `c`,
    all_tac, (* Call *)
    all_tac, (* JumpReg *)
    all_tac  (* Loc *)
  ]

local
  fun can_match [QUOTE s] =
        Lib.can (Term.match_term (Parse.Term [QUOTE (s ^ " : 'a asm")]))
    | can_match _ = raise ERR "" ""
  val syntax1 = #4 o HolKernel.syntax_fns1 "asm"
  val syntax2 = #4 o HolKernel.syntax_fns2 "asm"
  val syntax4 = #4 o HolKernel.syntax_fns4 "asm"
in
  val isInst = syntax1 "Inst"
  val isJump = syntax1 "Jump"
  val isJumpCmp = syntax4 "JumpCmp"
  val isCall = syntax1 "Call"
  val isJumpReg = syntax1 "JumpReg"
  val isLoc = syntax2 "Loc"
  val isSkip = can_match `asm$Inst (asm$Const _ _)`
  val isConst = can_match `asm$Inst (asm$Const _ _)`
  val isArith = can_match `asm$Inst (asm$Arith _)`
  val isFP = can_match `asm$Inst (asm$FP _)`
  val isMem = can_match `asm$Inst (asm$Mem _ _ _)`
  val isBinop = can_match `asm$Inst (asm$Arith (asm$Binop _ _ _ _))`
  val isShift = can_match `asm$Inst (asm$Arith (asm$Shift _ _ _ _))`
  val isAddCarry = can_match `asm$Inst (asm$Arith (asm$AddCarry _ _ _ _))`
  val isAddOverflow = can_match `asm$Inst (asm$Arith (asm$AddOverflow _ _ _ _))`
  val isSubOverflow = can_match `asm$Inst (asm$Arith (asm$SubOverflow _ _ _ _))`
end

end
