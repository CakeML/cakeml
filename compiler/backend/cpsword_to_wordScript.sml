(*
  this file compiles cpswordLang to wordLang
*)

open preamble
     wordLangTheory
     cpswordLangTheory;

local open backend_commonTheory in end; (* what is the effect of local open? *)

val _ = new_theory "cpsword_to_word";


val compile_exp = tDefine "compile_exp"`
  compile_exp (exp: 'a cpswordLang$exp) =
   case exp of
     | Const w => ((Const w) : 'a wordLang$exp)
     | Var n => Var n
     | Load e => Load (compile_exp e)
     | LoadByte adrexp => ARB
     | Op op es => Op op (MAP compile_exp es)
     | Shift sh exp n => Shift sh (compile_exp exp) n`
  (WF_REL_TAC `measure (exp_size ARB)`
   >> REPEAT STRIP_TAC
   >> IMP_RES_TAC MEM_IMP_exp_size
   >> TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
   >> DECIDE_TAC)


val compile_prog = Define`
  compile_prog (prog: 'a cpswordLang$prog)  =
   case prog of
     | Skip => (Skip:'a wordLang$prog)
     | Assign n e => Assign n (compile_exp e)
     | Store e n => Store (compile_exp e) n
     | StoreByte e n => ARB
     | Call retn trgt args hndl => ARB
     | Seq prog1 prog2 => Seq (compile_prog prog1) (compile_prog prog2)
     | If rlt n1 n2 prog1 prog2 => If rlt n1 (ARB n2) (compile_prog prog1) (compile_prog prog2)
     | Raise n => Raise n
     | Return n =>  Return n ARB
     | Tick => Tick
     | FFI ffi_index cptr clen ptr len names => FFI ffi_index cptr clen ptr len names`


val _ = export_theory();
