open preamble asmTheory;

val _ = new_theory "wordLang";

(* word lang = structured program with words, stack and memory *)

val _ = Datatype `
  store_name =
    NextFree | LastFree | CurrHeap | OtherHeap | AllocSize | AllocLeft`

val _ = Datatype `
  num_exp = Nat num
          | Add num_exp num_exp
          | Sub num_exp num_exp
          | Div2 num_exp
          | Exp2 num_exp
          | WordWidth ('a word)`

val _ = Datatype `
  exp = Const ('a word)
      | Var num
      | Lookup store_name
      | Load exp
      | Op binop (exp list)
      | Shift shift exp ('a num_exp)`

val _ = Datatype `
  prog = Skip
       | Move num ((num # num) list)
       | Inst ('a inst)
       | Assign num ('a exp)
       | Get num store_name
       | Set store_name ('a exp)
       | Store ('a exp) num
       | Call ((num # num_set # prog # num # num) option)
              (* return var, cut-set, return-handler code, labels l1,l2*)
              (num option) (* target of call *)
              (num list) (* arguments *)
              ((num # prog # num # num) option)
              (* handler: varname, exception-handler code, labels l1,l2*)
       | Seq prog prog
       | If cmp num ('a reg_imm) prog prog
       | Alloc num num_set
       | Raise num
       | Return num num
       | Tick `;

val _ = export_theory();
