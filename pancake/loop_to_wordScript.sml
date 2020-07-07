(*
  Compilation from looLang to wordLang.
*)
open preamble loopLangTheory
     wordLangTheory

val _ = new_theory "loop_to_word"

val _ = set_grammar_ancestry
        ["loopLang", "wordLang",
         "backend_common"];


Definition find_var_def:
  find_var ctxt v =
    case lookup v ctxt of
    | NONE => 0
    | SOME n => (n:num)
End

Definition find_reg_imm_def:
  (find_reg_imm ctxt (Imm w) = Imm w) ∧
  (find_reg_imm ctxt (Reg n) = Reg (find_var ctxt n))
End

Definition comp_exp_def :
  (comp_exp ctxt (loopLang$Const w) = wordLang$Const w) /\
  (comp_exp ctxt (Var n) = Var (find_var ctxt n)) /\
  (comp_exp ctxt (Lookup m) = Lookup (Temp m)) /\
  (comp_exp ctxt (Load exp) = Load (comp_exp ctxt exp)) /\
  (comp_exp ctxt (Shift s exp n) = Shift s (comp_exp ctxt exp) n) /\
  (comp_exp ctxt (Op op wexps) =
   let wexps = MAP (comp_exp ctxt) wexps in
   Op op wexps)
Termination
  WF_REL_TAC ‘measure (loopLang$exp_size (K 0) o SND)’ >>
  rw [] >>
  rename [‘MEM x xs’] >>
  Induct_on ‘xs’ >> fs [] >>
  fs [loopLangTheory.exp_size_def] >>
  rw [] >> fs []
End

Definition toNumSet_def:
  toNumSet [] = LN ∧
  toNumSet (n::ns) = insert n () (toNumSet ns)
End

Definition fromNumSet_def:
  fromNumSet t = MAP FST (toAList t)
End

Definition mk_new_cutset_def:
  mk_new_cutset ctxt (l:num_set) =
    insert 0 () (toNumSet (MAP (find_var ctxt) (fromNumSet l)))
End

Definition comp_def:
  (comp ctxt Skip l = (wordLang$Skip,l)) /\
  (comp ctxt (Assign n e) l =
     (Assign (find_var ctxt n) (comp_exp ctxt e),l)) /\
  (comp ctxt (Store e v) l =
     (Store (comp_exp ctxt e) (find_var ctxt v), l)) /\
  (comp ctxt (SetGlobal a e) l =
     (Set (Temp a) (comp_exp ctxt e), l)) /\
  (comp ctxt (LoadByte a v) l =
     (Inst (Mem Load8 (find_var ctxt v)
            (Addr (find_var ctxt a) 0w)), l)) /\
  (comp ctxt (StoreByte a v) l =
     (Inst (Mem Store8 (find_var ctxt v)
            (Addr (find_var ctxt a) 0w)), l)) /\
  (comp ctxt (Seq p q) l =
    let (wp,l) = comp ctxt p l in
     let (wq,l) = comp ctxt q l in
       (Seq wp wq,l)) /\
  (comp ctxt (If c n ri p q l1) l =
    let (wp,l) = comp ctxt p l in
     let (wq,l) = comp ctxt q l in
       (Seq (If c (find_var ctxt n) (find_reg_imm ctxt ri) wp wq) Tick,l)) /\
  (comp ctxt (Loop l1 body l2) l = (Skip,l)) /\ (* not present in input *)
  (comp ctxt Break l = (Skip,l)) /\ (* not present in input *)
  (comp ctxt Continue l = (Skip,l)) /\ (* not present in input *)
  (comp ctxt (Raise v) l = (Raise (find_var ctxt v),l)) /\
  (comp ctxt (Return v) l = (Return 0 (find_var ctxt v),l)) /\
  (comp ctxt Tick l = (Tick,l)) /\
  (comp ctxt (Mark p) l = comp ctxt p l) /\
  (comp ctxt Fail l = (Skip,l)) /\
  (comp ctxt (LocValue n m) l = (LocValue (find_var ctxt n) m,l))  /\
  (comp ctxt (Call ret dest args handler) l =
     let args = MAP (find_var ctxt) args in
       case ret of
       | NONE (* tail-call *) => (wordLang$Call NONE dest (0::args) NONE,l)
       | SOME (v,live) =>
         let v = find_var ctxt v in
         let live = mk_new_cutset ctxt live in
         let new_l = (FST l, SND l+1) in
           case handler of
           | NONE => (wordLang$Call (SOME (v,live,Skip,l)) dest args NONE, new_l)
           | SOME (n,p1,p2,_) =>
              let (p1,l1) = comp ctxt p1 new_l in
              let (p2,l1) = comp ctxt p2 l1 in
              let new_l = (FST l1, SND l1+1) in
                (Seq (Call (SOME (v,live,p2,l)) dest args
                   (SOME (find_var ctxt n,p1,l1))) Tick, new_l)) /\
   (comp ctxt (FFI f ptr1 len1 ptr2 len2 live) l =
      let live = mk_new_cutset ctxt live in
        (FFI f (find_var ctxt ptr1) (find_var ctxt len1)
               (find_var ctxt ptr2) (find_var ctxt len2) live,l))
End

Definition make_ctxt_def:
  make_ctxt n [] l = l ∧
  make_ctxt n (x::xs) l = make_ctxt (n+2:num) xs (insert x n l)
End

Definition compile_def:
  compile name params body =
    let vs = fromNumSet (difference (acc_vars body LN) (toNumSet params)) in
    let ctxt = make_ctxt 2 (params ++ vs) LN in
      FST (comp ctxt body (name,2))
End

val _ = export_theory();
