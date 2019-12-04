(*
  Computes the call graph for wordLang program with an acyclic call
  graph. This graph is in turn used to compute the max stack depth
  used by the wordLang program.
*)
open preamble wordLangTheory;

val _ = new_theory "word_depth";

(* representation of acyclic call graph, i.e. call tree *)

Datatype:
  call_tree = Leaf
            | Unknown
            | Call num call_tree
            | Branch call_tree call_tree
End

(* computing the max stack depth *)

Definition max_depth_def:
  max_depth frame_sizes Leaf = SOME 0 /\
  max_depth frame_sizes Unknown = NONE /\
  max_depth frame_sizes (Branch t1 t2) =
    OPTION_MAP2 MAX (max_depth frame_sizes t1) (max_depth frame_sizes t2) /\
  max_depth frame_sizes (Call n t) =
    OPTION_MAP2 (+) (lookup n frame_sizes) (max_depth frame_sizes t)
End

(* computing the call graph *)

Definition mk_Branch_def:
  mk_Branch t1 t2 =
    if t1 = t2 then t1 else
    if t1 = Leaf then t2 else
    if t2 = Leaf then t1 else
    if t1 = Unknown then t1 else
    if t2 = Unknown then t2 else
      Branch t1 t2
End

Definition call_graph_def:
  (call_graph funs n ns total (Seq p1 p2) =
     mk_Branch (call_graph funs n ns total p1) (call_graph funs n ns total p2)) /\
  (call_graph funs n ns total (If _ _ _ p1 p2) =
     mk_Branch (call_graph funs n ns total p1) (call_graph funs n ns total p2)) /\
  (call_graph funs n ns total (Call ret dest args handler) =
     case dest of
     | NONE => Unknown
     | SOME d =>
       case lookup d funs of
       | NONE => Unknown
       | SOME (a:num,body) =>
         case ret of
         | NONE =>
           (if MEM d ns then Leaf else
            if LENGTH ns < total then
              mk_Branch (Call d (Leaf))
                (call_graph funs d (d::ns) total body)
            else Leaf)
         | SOME (_,_,ret_prog,_,_) =>
           if lookup n funs = NONE then Unknown else
             let new_funs = delete d funs in
             let t = Branch (Call n (Call d Leaf))
                      (mk_Branch (Call n (call_graph new_funs d [d] total body))
                                 (call_graph funs n ns total ret_prog)) in
               case handler of NONE => t
               | SOME (_,p,_,_) => mk_Branch t (call_graph funs n ns total p)) /\
  (call_graph funs n ns total (MustTerminate p) = call_graph funs n ns total p) /\
  (call_graph funs n ns total (Alloc _ _) = Call n Leaf) /\
  (call_graph funs n ns total (Install _ _ _ _ _) = Unknown) /\
  (call_graph funs n ns _ _ = Leaf)
Termination
  WF_REL_TAC `(inv_image (measure I LEX measure I LEX measure I)
      (\(funs,n,ns,total,p). (size funs, total - LENGTH ns, prog_size (K 0) p)))`
  \\ rpt strip_tac \\ fs [size_delete]
  \\ imp_res_tac miscTheory.lookup_zero \\ fs []
End

val _ = export_theory();
