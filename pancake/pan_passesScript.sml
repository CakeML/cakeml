(*
  Reformulates compile definition to expose the result of each internal
  compiler pass
*)

open preamble backendTheory backend_passesTheory presLangTheory;
open pan_to_targetTheory;

val _ = new_theory"pan_passes";

val _ = set_grammar_ancestry ["pan_to_target","backend_passes"];

Datatype:
  any_pan_prog =
      Pan ((mlstring # (mlstring # shape) list # 'a panLang$prog) list)
    | Crep ((mlstring # num list # α crepLang$prog) list)
    | Loop ((num # num list # α loopLang$prog) list) (mlstring sptree$num_map)
    | Cake ('a backend_passes$any_prog)
End

Definition pan_to_target_all_def:
  pan_to_target_all (c:'a config) prog =
    let
      prog0 = case SPLITP (λ(n,e,p,b). n = «main») prog of
              | ([],ys) => ys
              | (xs,[]) => («main»,F,[],Return (Const 0w))::xs
              | (xs,y::ys) => y::xs ++ ys
    in
      if ¬NULL prog0 ∧ FST (SND (HD prog0)) then ([],NONE) else
        let
          prog1 = MAP (λ(n,e,p,b). (n,p,b)) prog0;
          ps = [(«initial pancake program»,Pan prog1)];
          prog_a = pan_simp$compile_prog prog1;
          ps = ps ++ [(«after pan_simp»,Pan prog_a)];
          prog_b0 = pan_to_crep$compile_prog prog_a;
          ps = ps ++ [(«after pan_to_crep»,Crep prog_b0)];
          prog_b = MAP (λ(n,ps,e). (n,ps,crep_arith$simp_prog e)) prog_b0;
          ps = ps ++ [(«after crep_arith»,Crep prog_b)];
          fnums = GENLIST (λn. n + first_name) (LENGTH prog_b);
          funcs = make_funcs prog_b;
          target = c.lab_conf.asm_conf.ISA;
          comp = comp_func target funcs;
          prog_b1 = MAP2 (λn (name,params,body).
                      (n,(GENLIST I ∘ LENGTH) params, comp params body)) fnums prog_b;
          prog_c = MAP (λ(name,params,body). (name,params,loop_live$optimise body)) prog_b1;
          prog_c1 = loop_remove$comp_prog prog_c;
          prog2 = loop_to_word$compile_prog prog_c1;
          names = fromAList (ZIP (QSORT $< (MAP FST prog2),MAP FST prog1));
          names = union (fromAList (word_to_stack$stub_names () ++
                                    stack_alloc$stub_names () ++
                                    stack_remove$stub_names ())) names;
          ps = ps ++ [(«after crep_to_loop»,Loop prog_b1 names)];
          ps = ps ++ [(«after loop_optimise»,Loop prog_c names)];
          ps = ps ++ [(«after loop_remove»,Loop prog_c1 names)];
          ps = ps ++ [(«after loop_to_word»,Cake (Word prog2 names))];
          c = c with exported := MAP FST (FILTER (FST ∘ SND) prog);
          (ps1,out) = from_word_0_all [] c names prog2
        in
          (ps ++ MAP (λ(n,p). (n,Cake p)) ps1,out)
End

Triviality MAP2_MAP:
  ∀xs ys. MAP2 g xs (MAP f ys) = MAP2 (λx y. g x (f y)) xs ys
Proof
  Induct \\ Cases_on ‘ys’ \\ gvs []
QED

Triviality MAP_MAP2:
  ∀xs ys. MAP f (MAP2 g xs ys) = MAP2 (λx y. f (g x y)) xs ys
Proof
  Induct \\ Cases_on ‘ys’ \\ gvs []
QED

Triviality make_funcs_MAP:
  ∀xs. make_funcs (MAP (λ(n,ps,e). (n,ps,f e)) xs) = crep_to_loop$make_funcs xs
Proof
  simp [crep_to_loopTheory.make_funcs_def]
  \\ qspec_tac (‘first_name’,‘nn’)
  \\ Induct_on ‘xs’ \\ gvs []
  \\ PairCases \\ gvs [] \\ gvs [GENLIST_CONS]
  \\ gvs [o_DEF,ADD1] \\ rw []
  \\ pop_assum $ qspec_then ‘nn+1’ assume_tac
  \\ gvs [GSYM ADD1,ADD_CLAUSES,AC ADD_COMM ADD_ASSOC]
  \\ once_rewrite_tac [ADD_COMM] \\ gvs []
QED

Theorem compile_prog_eq_pan_to_target_all:
  compile_prog c p = SND (pan_to_target_all c p)
Proof
  gvs [compile_prog_eq,pan_to_target_all_def,UNCURRY]
  \\ qmatch_goalsub_abbrev_tac ‘NULL prog’
  \\ IF_CASES_TAC >- gvs []
  \\ pop_assum kall_tac
  \\ gvs [backend_passesTheory.from_word_0_thm,pan_to_wordTheory.compile_prog_def,
          loop_to_wordTheory.compile_def,crep_to_loopTheory.compile_prog_def,
          MAP_MAP2,MAP2_MAP,make_funcs_MAP]
  \\ gvs [LAMBDA_PROD,loop_to_wordTheory.compile_def]
QED

(* pan *)

Definition shape_to_str_def:
  shape_to_str One = strlit "1" ∧
  shape_to_str (Comb []) = strlit "<>" ∧
  shape_to_str (Comb (x::xs)) =
    concat (strlit "<" :: shape_to_str x ::
            MAP (λx. strlit "," ^ x) (MAP shape_to_str xs) ++
            [strlit ">"])
Termination
  WF_REL_TAC ‘measure shape_size’
End

Definition opsize_to_display_def:
  opsize_to_display Op8 = empty_item (strlit "byte") ∧
  opsize_to_display OpW = empty_item (strlit "word") ∧
  opsize_to_display Op32 = empty_item (strlit "halfword")
End

Definition insert_es_def:
  insert_es (String n) xs = Item NONE n xs ∧
  insert_es x _ = x
End

Definition pan_exp_to_display_def:
  (pan_exp_to_display (panLang$Const v)
    = item_with_word (strlit "Const") v) ∧
  (pan_exp_to_display (Var n)
    = Item NONE (strlit "Var") [String n]) ∧
  (pan_exp_to_display (Label n)
    = Item NONE (strlit "Label") [String n]) ∧
  (pan_exp_to_display BaseAddr
    = Item NONE (strlit "BaseAddr") []) ∧
  (pan_exp_to_display (panLang$Load shape exp2)
    = Item NONE (strlit "MemLoad")
           [String (shape_to_str shape);
            pan_exp_to_display exp2]) ∧
  (pan_exp_to_display (panLang$LoadByte exp2)
    = Item NONE (strlit "MemLoadByte") [pan_exp_to_display exp2]) ∧
  (pan_exp_to_display (Struct xs)
    = Item NONE (strlit "Struct") (MAP pan_exp_to_display xs)) ∧
  (pan_exp_to_display (Cmp cmp x1 x2)
    = insert_es (asm_cmp_to_display cmp)
                [pan_exp_to_display x1; pan_exp_to_display x2]) ∧
  (pan_exp_to_display (Op b xs)
    = insert_es (asm_binop_to_display b) (MAP pan_exp_to_display xs)) ∧
  (pan_exp_to_display (Panop p xs)
    = case p of
      | Mul => Item NONE (strlit "Mul") (MAP pan_exp_to_display xs)) ∧
  (pan_exp_to_display (Field n e)
    = Item NONE (strlit "Field") [num_to_display n; pan_exp_to_display e]) ∧
  (pan_exp_to_display (Shift sh e n)
    = insert_es (shift_to_display sh) [pan_exp_to_display e; num_to_display n])
Termination
  WF_REL_TAC `measure (panLang$exp_size ARB)`
End

Definition dest_annot_def:
  dest_annot (Annot str) = SOME str /\
  dest_annot _ = NONE
End

(* treat (Seq (Annot _) _) as a special case, and don't flatten it *)
Definition pan_seqs_def:
  pan_seqs z =
    case z of
    | panLang$Seq x y => (case dest_annot x of SOME _ => List [z]
        | _ => Append (pan_seqs x) (pan_seqs y))
    | _ => List [z]
End

Triviality MEM_append_pan_seqs:
  ∀prog1 a.
    MEM a (append (pan_seqs prog1)) ⇒
    prog_size ARB a ≤ prog_size ARB prog1
Proof
  Induct \\ simp [Once pan_seqs_def]
  \\ every_case_tac
  \\ gvs [panLangTheory.prog_size_def]
  \\ rw [] \\ res_tac \\ fs []
QED

Definition pan_prog_to_display_def:
  (pan_prog_to_display panLang$Skip = empty_item (strlit "skip")) ∧
  (pan_prog_to_display (ShMemLoad s v e) =
     Item NONE (strlit "shared_mem_load")
          [opsize_to_display s;
           String v;
           pan_exp_to_display e]) ∧
  (pan_prog_to_display (ShMemStore s e1 e2) =
     Item NONE (strlit "shared_mem_store")
          [opsize_to_display s;
           pan_exp_to_display e1;
           pan_exp_to_display e2]) ∧
  (pan_prog_to_display (ExtCall f e1 e2 e3 e4) =
     Item NONE (strlit "ext_call")
          [String f;
           pan_exp_to_display e1;
           pan_exp_to_display e2;
           pan_exp_to_display e3;
           pan_exp_to_display e4]) ∧
  (pan_prog_to_display (If e p1 p2) =
     Item NONE (strlit "if")
          [pan_exp_to_display e;
           pan_prog_to_display p1;
           pan_prog_to_display p2]) ∧
  (pan_prog_to_display (While e p) =
     Item NONE (strlit "while")
          [pan_exp_to_display e;
           pan_prog_to_display p]) ∧
  (pan_prog_to_display (Dec n e p) =
     Item NONE (strlit "dec")
          [Tuple [String n; String (strlit ":="); pan_exp_to_display e];
           pan_prog_to_display p]) ∧
  (pan_prog_to_display (Assign n exp) =
     Tuple [String n;
            String (strlit ":=");
            pan_exp_to_display exp]) ∧
  (pan_prog_to_display (Store e1 e2) = Tuple
    [String (strlit "mem"); pan_exp_to_display e1;
     String (strlit ":="); pan_exp_to_display e2]) ∧
  (pan_prog_to_display (StoreByte e1 e2) = Tuple
    [String (strlit "mem"); pan_exp_to_display e1;
     String (strlit ":="); String (strlit "byte"); pan_exp_to_display e2]) ∧
  (pan_prog_to_display (Annot str) = Item NONE (strlit "annot") [String str]) ∧
  (pan_prog_to_display Tick = empty_item (strlit "tick")) ∧
  (pan_prog_to_display Break = empty_item (strlit "break")) ∧
  (pan_prog_to_display Continue = empty_item (strlit "continue")) ∧
  (pan_prog_to_display (Return e) =
     Item NONE (strlit "return") [pan_exp_to_display e]) ∧
  (pan_prog_to_display (Raise n e) =
     Item NONE (strlit "raise") [String n; pan_exp_to_display e]) ∧
  (pan_prog_to_display (Seq prog1 prog2) =
     let xs = append (Append (pan_seqs prog1) (pan_seqs prog2)) in
     separate_lines (strlit "seq") (MAP pan_prog_to_display xs)) ∧
  (pan_prog_to_display (panLang$Call ret_opt dest args) =
     case ret_opt of
     | NONE =>
         Item NONE (strlit "tail_call")
              [pan_exp_to_display dest;
               Tuple (MAP pan_exp_to_display args)]
     | SOME (NONE,handler) =>
         Item NONE (strlit "call")
              [pan_exp_to_display dest;
               Tuple (MAP pan_exp_to_display args);
               pan_prog_to_display_handler handler]
     | SOME (SOME v,handler) =>
         Tuple [String v;
                String (strlit ":=");
                Item NONE (strlit "call")
                     [pan_exp_to_display dest;
                      Tuple (MAP pan_exp_to_display args);
                      pan_prog_to_display_handler handler]]) ∧
  (pan_prog_to_display (DecCall v shape dest args p) =
     Item NONE (strlit "dec")
          [Tuple [String v;
                  String (strlit ":=");
                  Item NONE (strlit "call")
                       [pan_exp_to_display dest;
                        Tuple (MAP pan_exp_to_display args);
                        String (shape_to_str shape)]];
           pan_prog_to_display p]) ∧
  (pan_prog_to_display_handler NONE = empty_item (strlit "no_handler")) ∧
  (pan_prog_to_display_handler (SOME (v1,v2,p)) =
    Item NONE (strlit "handler")
      [Tuple [String v1; String v2; pan_prog_to_display p]])
Termination
  WF_REL_TAC ‘measure $ \x. case x of
        | INL p => panLang$prog_size ARB p
        | INR p => panLang$prog3_size ARB p’
  \\ rw [] \\ imp_res_tac MEM_append_pan_seqs \\ fs []
End

Definition pan_fun_to_display_def:
  pan_fun_to_display (nm,args,body) =
    Tuple
      [String «func»; String nm;
       Tuple (MAP (λ(s,shape). Tuple [String s;
                                      String (strlit ":");
                                      String (shape_to_str shape)]) args);
       pan_prog_to_display body]
End

Definition pan_to_strs_def:
  pan_to_strs xs =
    map_to_append
      (v2strs «\n\n» ∘ display_to_str_tree ∘ pan_fun_to_display) xs
End

(* crep *)

Definition crep_exp_to_display_def:
  (crep_exp_to_display (crepLang$Const v)
    = item_with_word (strlit "Const") v) ∧
  (crep_exp_to_display (LoadGlob w)
    = item_with_word (strlit "LoadGlob") w) ∧
  (crep_exp_to_display (Var n)
    = Item NONE (strlit "Var") [num_to_display n]) ∧
  (crep_exp_to_display (Label n)
    = Item NONE (strlit "Label") [String n]) ∧
  (crep_exp_to_display BaseAddr
    = Item NONE (strlit "BaseAddr") []) ∧
  (crep_exp_to_display (crepLang$Load exp2)
    = Item NONE (strlit "MemLoad") [crep_exp_to_display exp2]) ∧
  (crep_exp_to_display (crepLang$LoadByte exp2)
    = Item NONE (strlit "MemLoadByte") [crep_exp_to_display exp2]) ∧
  (crep_exp_to_display (Cmp cmp x1 x2)
    = insert_es (asm_cmp_to_display cmp)
                [crep_exp_to_display x1; crep_exp_to_display x2]) ∧
  (crep_exp_to_display (Op b xs)
    = insert_es (asm_binop_to_display b) (MAP crep_exp_to_display xs)) ∧
  (crep_exp_to_display (Crepop p xs)
    = case p of
      | Mul => Item NONE (strlit "Mul") (MAP crep_exp_to_display xs)) ∧
  (crep_exp_to_display (Shift sh e n)
    = insert_es (shift_to_display sh) [crep_exp_to_display e; num_to_display n])
Termination
  WF_REL_TAC `measure (crepLang$exp_size ARB)`
End

Definition crep_seqs_def:
  crep_seqs z =
    case z of
    | crepLang$Seq x y => Append (crep_seqs x) (crep_seqs y)
    | _ => List [z]
End

Triviality MEM_append_crep_seqs:
  ∀prog1 a.
    MEM a (append (crep_seqs prog1)) ⇒
    prog_size ARB a ≤ prog_size ARB prog1
Proof
  Induct \\ simp [Once crep_seqs_def]
  \\ gvs [crepLangTheory.prog_size_def]
  \\ rw [] \\ res_tac \\ fs []
QED

Definition crep_prog_to_display_def:
  (crep_prog_to_display crepLang$Skip = empty_item (strlit "skip")) ∧
  (crep_prog_to_display (ShMem mop v e) =
     let prefix = (case mop of
                   | Load => [String (strlit "load"); String (strlit "word")]
                   | Load8 => [String (strlit "load"); String (strlit "byte")]
                   | Load32 => [String (strlit "load"); String (strlit "halfword")]
                   | Store => [String (strlit "store"); String (strlit "word")]
                   | Store8 => [String (strlit "store"); String (strlit "byte")]
                   | Store32 => [String (strlit "store"); String (strlit "halfword")]) in
       Item NONE (strlit "shared_mem")
            (prefix ++ [num_to_display v; crep_exp_to_display e])) ∧
  (crep_prog_to_display (ExtCall f e1 e2 e3 e4) =
     Item NONE (strlit "ext_call")
          [String f;
           num_to_display e1;
           num_to_display e2;
           num_to_display e3;
           num_to_display e4]) ∧
  (crep_prog_to_display (StoreGlob w e) =
     Item NONE (strlit "store_glob")
          [word_to_display w;
           crep_exp_to_display e]) ∧
  (crep_prog_to_display (If e p1 p2) =
     Item NONE (strlit "if")
          [crep_exp_to_display e;
           crep_prog_to_display p1;
           crep_prog_to_display p2]) ∧
  (crep_prog_to_display (While e p) =
     Item NONE (strlit "while")
          [crep_exp_to_display e;
           crep_prog_to_display p]) ∧
  (crep_prog_to_display (Dec n e p) =
     Item NONE (strlit "dec")
          [Tuple [num_to_display n; String (strlit ":="); crep_exp_to_display e];
           crep_prog_to_display p]) ∧
  (crep_prog_to_display (Assign n exp) =
     Tuple [num_to_display n;
            String (strlit ":=");
            crep_exp_to_display exp]) ∧
  (crep_prog_to_display (Store e1 e2) = Tuple
    [String (strlit "mem"); crep_exp_to_display e1;
     String (strlit ":="); crep_exp_to_display e2]) ∧
  (crep_prog_to_display (StoreByte e1 e2) = Tuple
    [String (strlit "mem"); crep_exp_to_display e1;
     String (strlit ":="); String (strlit "byte"); crep_exp_to_display e2]) ∧
  (crep_prog_to_display Tick = empty_item (strlit "tick")) ∧
  (crep_prog_to_display Break = empty_item (strlit "break")) ∧
  (crep_prog_to_display Continue = empty_item (strlit "continue")) ∧
  (crep_prog_to_display (Return e) =
     Item NONE (strlit "return") [crep_exp_to_display e]) ∧
  (crep_prog_to_display (Raise w) =
     item_with_word (strlit "raise") w) ∧
  (crep_prog_to_display (Seq prog1 prog2) =
    (let xs = append (Append (crep_seqs prog1) (crep_seqs prog2)) in
       separate_lines (strlit "seq") (MAP crep_prog_to_display xs))) ∧
  (crep_prog_to_display (crepLang$Call ret_opt dest args) =
     case ret_opt of
     | NONE =>
         Item NONE (strlit "tail_call")
              [crep_exp_to_display dest;
               Tuple (MAP crep_exp_to_display args)]
     | SOME (NONE,p,handler) =>
         Item NONE (strlit "call")
              [crep_exp_to_display dest;
               Tuple (MAP crep_exp_to_display args);
               crep_prog_to_display p;
               crep_prog_to_display_handler handler]
     | SOME (SOME v,p,handler) =>
         Tuple [num_to_display v;
                String (strlit ":=");
                Item NONE (strlit "call")
                     [crep_exp_to_display dest;
                      Tuple (MAP crep_exp_to_display args);
                      crep_prog_to_display p;
                      crep_prog_to_display_handler handler]]) ∧
  (crep_prog_to_display_handler NONE = empty_item (strlit "no_handler")) ∧
  (crep_prog_to_display_handler (SOME (w,p)) =
    Item NONE (strlit "handler")
      [Tuple [word_to_display w; crep_prog_to_display p]])
Termination
  WF_REL_TAC ‘measure $ \x. case x of
        | INL p => crepLang$prog_size ARB p
        | INR p => crepLang$prog4_size ARB p’
  \\ rw [] \\ imp_res_tac MEM_append_crep_seqs \\ fs []
End

Definition crep_fun_to_display_def:
  crep_fun_to_display (nm,args,body) =
    Tuple
      [String «func»; String nm;
       Tuple (MAP num_to_display args);
       crep_prog_to_display body]
End

Definition crep_to_strs_def:
  crep_to_strs xs =
    map_to_append
      (v2strs «\n\n» ∘ display_to_str_tree ∘ crep_fun_to_display) xs
End

(* loop *)

Definition loop_exp_to_display_def:
  (loop_exp_to_display (loopLang$Const v)
    = item_with_word (strlit "Const") v) ∧
  (loop_exp_to_display (Var n)
    = item_with_num (strlit "Var") n) ∧
  (loop_exp_to_display BaseAddr
    = Item NONE (strlit "BaseAddr") []) ∧
  (loop_exp_to_display (Lookup st)
    = item_with_word (strlit "Lookup") st) ∧
  (loop_exp_to_display (Load exp2)
    = Item NONE (strlit "MemLoad") [loop_exp_to_display exp2]) /\
  (loop_exp_to_display (Op bop exs)
    = Item NONE (strlit "Op") (asm_binop_to_display bop
        :: MAP loop_exp_to_display exs)) /\
  (loop_exp_to_display (Shift sh exp num)
    = Item NONE (strlit "Shift") [
      shift_to_display sh;
      loop_exp_to_display exp;
      num_to_display num
    ])
Termination
  WF_REL_TAC `measure (loopLang$exp_size ARB)`
End

Definition loop_seqs_def:
  loop_seqs z =
    case z of
    | loopLang$Seq x y => Append (loop_seqs x) (loop_seqs y)
    | _ => List [z]
End

Triviality MEM_append_loop_seqs:
  ∀prog1 a.
    MEM a (append (loop_seqs prog1)) ⇒
    prog_size ARB a ≤ prog_size ARB prog1
Proof
  Induct \\ simp [Once loop_seqs_def]
  \\ gvs [loopLangTheory.prog_size_def]
  \\ rw [] \\ res_tac \\ fs []
QED

Definition loop_prog_to_display_def:
  (loop_prog_to_display ns Skip = empty_item (strlit "skip")) ∧
  (loop_prog_to_display ns (Arith a) =
    case a of
    | LLongMul n1 n2 n3 n4 =>
        item_with_nums (strlit "long_mul") [n1;n2;n3;n4]
    | LLongDiv n1 n2 n3 n4 n5 =>
        item_with_nums (strlit "long_div") [n1;n2;n3;n4;n5]
    | LDiv n1 n2 n3 =>
        item_with_nums (strlit "div") [n1;n2;n3]) ∧
  (loop_prog_to_display ns (Assign n exp) =
     Tuple [num_to_display n;
            String (strlit ":=");
            loop_exp_to_display exp]) ∧
  (loop_prog_to_display ns (SetGlobal w exp) =
     Item NONE (strlit "set_global")
          [word_to_display w;
           loop_exp_to_display exp]) ∧
  (loop_prog_to_display ns (Seq prog1 prog2) =
    (let xs = append (Append (loop_seqs prog1) (loop_seqs prog2)) in
       separate_lines (strlit "seq") (MAP (loop_prog_to_display ns) xs))) /\
  (loop_prog_to_display ns (FFI nm n1 n2 n3 n4 ms) =
    Item NONE (strlit "ffi") (string_imp nm :: MAP num_to_display [n1; n2; n3; n4]
        ++ [num_set_to_display ms])) ∧
  (loop_prog_to_display ns (Raise n) = item_with_num (strlit "raise") n) ∧
  (loop_prog_to_display ns (Return n) = item_with_num (strlit "return") n) ∧
  (loop_prog_to_display ns Tick = empty_item (strlit "tick")) ∧
  (loop_prog_to_display ns Break = empty_item (strlit "break")) ∧
  (loop_prog_to_display ns Continue = empty_item (strlit "continue")) ∧
  (loop_prog_to_display ns Fail = empty_item (strlit "fail")) ∧
  (loop_prog_to_display ns (LoadByte n1 n2) =
    item_with_nums (strlit "load_byte") [n1;n2]) ∧
  (loop_prog_to_display ns (StoreByte n1 n2) =
    item_with_nums (strlit "store_byte") [n1;n2]) ∧
  (loop_prog_to_display ns (LocValue n1 n2) =
    Item NONE (strlit "loc_value") [String (attach_name ns (SOME n1)); num_to_display n2]) ∧
  (loop_prog_to_display ns (ShMem mop n e) = Tuple
    [String (strlit "share_mem"); asm_memop_to_display mop;
     num_to_display n; loop_exp_to_display e]) ∧
  (loop_prog_to_display ns (If cmp n reg p1 p2 ms) =
    Item NONE (strlit "if")
      [Tuple [asm_cmp_to_display cmp;
              num_to_display n;
              asm_reg_imm_to_display reg];
       loop_prog_to_display ns p1; loop_prog_to_display ns p2; num_set_to_display ms]) ∧
  (loop_prog_to_display ns (Loop ms1 p ms2) =
    Item NONE (strlit "loop")
      [num_set_to_display ms1;
       loop_prog_to_display ns p;
       num_set_to_display ms2]) ∧
  (loop_prog_to_display ns (Mark prog) = Item NONE (strlit "mark")
    [loop_prog_to_display ns prog]) ∧
  (loop_prog_to_display ns (Store exp n) = Tuple
    [String (strlit "mem"); loop_exp_to_display exp;
     String (strlit ":="); num_to_display n]) ∧
  (loop_prog_to_display ns (Call a b c d) =
     case a of
     | NONE => Item NONE (strlit "tail_call")
                 [option_to_display (λn. String (attach_name ns (SOME n))) b;
                  list_to_display num_to_display c]
     | SOME (n,ms) =>
         Tuple [num_to_display n;
                String (strlit ":=");
                Item NONE (strlit "call")
                 [option_to_display (λn. String (attach_name ns (SOME n))) b;
                  list_to_display num_to_display c;
                  num_set_to_display ms;
                  loop_prog_to_display_handler ns d]]) ∧
  (loop_prog_to_display_handler ns NONE = empty_item (strlit "no_handler")) /\
  (loop_prog_to_display_handler ns (SOME (n1, p1, p2, ms)) =
    Item NONE (strlit "handler")
      [Tuple
         [num_to_display n1;
          loop_prog_to_display ns p1;
          loop_prog_to_display ns p2;
          num_set_to_display ms]])
Termination
  WF_REL_TAC ‘measure $ \x. case x of
        | INL (_,p) => loopLang$prog_size ARB p
        | INR (_,p) => loopLang$prog1_size ARB p’
  \\ rw [] \\ imp_res_tac MEM_append_loop_seqs \\ fs []
End

Definition loop_fun_to_display_def:
  loop_fun_to_display names (n,args,body) =
    Tuple
      [String «func»; String (attach_name names (SOME n));
       Tuple (MAP num_to_display args);
       loop_prog_to_display names body]
End

Definition loop_to_strs_def:
  loop_to_strs names xs =
    map_to_append
      (v2strs «\n\n» ∘ display_to_str_tree ∘ loop_fun_to_display names) xs
End

Definition any_pan_prog_pp_def:
  any_pan_prog_pp x = case x of
    | Pan p => pan_to_strs p
    | Crep p => crep_to_strs p
    | Loop p ns => loop_to_strs ns p
    | Cake p => backend_passes$any_prog_pp p
End

Definition pan_compile_tap_def:
  pan_compile_tap (c:'a config) p =
    if c.tap_conf.explore_flag then
      let (ps,out) = pan_to_target_all c p in
        (out, FOLDR (pp_with_title any_pan_prog_pp) Nil ps)
    else (compile_prog c p, Nil)
End

Theorem compile_alt:
  compile_prog c p = FST (pan_compile_tap c p)
Proof
  rw [pan_compile_tap_def]
  \\ mp_tac compile_prog_eq_pan_to_target_all
  \\ pairarg_tac \\ gvs []
QED

val _ = export_theory();
