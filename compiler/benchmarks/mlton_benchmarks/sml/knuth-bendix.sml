(* From the SML/NJ benchmark suite. *)
signature BMARK =
  sig
    val doit : int -> unit
    val testit : TextIO.outstream -> unit
  end;
(* knuth-bendix.sml
 *)

signature KB =
  sig
    datatype term = Var of int | Term of string * term list;
    datatype ordering = Greater | Equal | NotGE;
    val rpo: (string -> string -> ordering) ->
           ((term * term -> ordering) -> term * term -> ordering) ->
           term * term -> ordering;
    val lex_ext:  (term * term -> ordering) -> term * term -> ordering;
    val kb_complete:
      (term * term -> bool) -> (int * (int * (term * term))) list ->
      ('a * ('b * (term * term))) list -> unit;
    include BMARK
  end;

structure Main : KB =
  struct

    val name = "Knuth-Bendix"

    fun length l = let
          fun j(k, nil) = k
            | j(k, a::x) = j(k+1,x)
          in
            j(0,l)
          end
    fun op @ (nil, l) = l
      | op @ (a::r, l) = a :: (r@l)
    fun rev l = let
          fun f (nil, h) = h
            | f (a::r, h) = f(r, a::h)
          in
            f(l,nil)
          end
    fun app f = let
          fun app_rec [] = ()
            | app_rec (a::L) = (f a; app_rec L)
        in
          app_rec
        end
    fun map f = let
          fun map_rec [] = []
            | map_rec (a::L) = f a :: map_rec L
          in
            map_rec
          end

(******* Quelques definitions du prelude CAML **************)

    exception Failure of string;

    fun failwith s = raise(Failure s)

    fun fst (x,y) = x
    and snd (x,y) = y


fun it_list f =
  let fun it_rec a [] = a
        | it_rec a (b::L) = it_rec (f a b) L
  in it_rec
  end

fun it_list2 f =
  let fun it_rec  a    []       []    = a
        | it_rec  a (a1::L1) (a2::L2) = it_rec (f a (a1,a2)) L1 L2
        | it_rec  _    _        _     = failwith "it_list2"
  in it_rec
  end

fun exists p =
  let fun exists_rec []  = false
        | exists_rec (a::L) = (p a) orelse (exists_rec L)
  in exists_rec
  end

fun for_all p =
  let fun for_all_rec []  = true
        | for_all_rec (a::L) = (p a) andalso (for_all_rec L)
  in for_all_rec
  end

fun rev_append   []    L  = L
  | rev_append (x::L1) L2 = rev_append L1 (x::L2)

fun try_find f =
  let fun try_find_rec  []    = failwith "try_find"
        | try_find_rec (a::L) = (f a) handle Failure _ => try_find_rec L
  in try_find_rec
  end

fun partition p =
  let fun part_rec   []   = ([],[])
        | part_rec (a::L) =
            let val (pos,neg) = part_rec L in
              if p a then  ((a::pos), neg) else (pos, (a::neg))
            end
  in part_rec
  end

(* 3- Les ensembles et les listes d'association *)

fun mem a =
  let fun mem_rec [] = false
        | mem_rec (b::L) = (a=b) orelse mem_rec L
  in mem_rec
  end

fun union L1 L2 =
  let fun union_rec [] = L2
        | union_rec (a::L) =
            if mem a L2 then union_rec L else a :: union_rec L
  in union_rec L1
  end

fun mem_assoc a =
  let fun mem_rec [] = false
        | mem_rec ((b,_)::L) = (a=b) orelse mem_rec L
  in mem_rec
  end

fun assoc a =
  let fun assoc_rec [] = failwith "find"
        | assoc_rec ((b,d)::L) = if a=b then d else assoc_rec L
  in assoc_rec
  end

(* 4- Les sorties *)

fun print s = TextIO.output(TextIO.stdOut, s)
fun print _ = ()
val print_string = print
val print_num = print o Int.toString
fun print_newline () = print "\n";
fun message s = (print s; print "\n");

(* 5- Les ensembles *)

fun union L1 =
  let fun union_rec [] = L1
        | union_rec (a::L) = if mem a L1 then union_rec L else a :: union_rec L
  in union_rec
  end

(****************** Term manipulations *****************)

datatype term
  = Var of int
  | Term of string * term list

fun vars (Var n) = [n]
  | vars (Term(_,L)) = vars_of_list L
and vars_of_list [] = []
  | vars_of_list (t::r) = union (vars t) (vars_of_list r)

fun substitute subst =
  let fun subst_rec (Term(oper,sons)) = Term(oper, map subst_rec sons)
        | subst_rec (t as (Var n))     = (assoc n subst) handle Failure _ => t
  in subst_rec
  end

fun change f =
  let fun change_rec (h::t) n = if n=1 then f h :: t
                                       else h :: change_rec t (n-1)
        | change_rec _ _      = failwith "change"
  in change_rec
  end

(* Term replacement replace M u N => M[u<-N] *)
fun replace M u N =
  let fun reprec (_, []) = N
        | reprec (Term(oper,sons), (n::u)) =
             Term(oper, change (fn P => reprec(P,u)) sons n)
        | reprec _ = failwith "replace"
  in reprec(M,u)
  end

(* matching = - : (term -> term -> subst) *)
fun matching term1 term2 =
  let fun match_rec subst (Var v, M) =
          if mem_assoc v subst then
            if M = assoc v subst then subst else failwith "matching"
          else
            (v,M) :: subst
        | match_rec subst (Term(op1,sons1), Term(op2,sons2)) =
          if op1 = op2 then it_list2 match_rec subst sons1 sons2
                       else failwith "matching"
        | match_rec _ _ = failwith "matching"
  in match_rec [] (term1,term2)
  end

(* A naive unification algorithm *)

fun compsubst subst1 subst2 =
  (map (fn (v,t) => (v, substitute subst1 t)) subst2) @ subst1

fun occurs n =
  let fun occur_rec (Var m) = (m=n)
        | occur_rec (Term(_,sons)) = exists occur_rec sons
  in occur_rec
  end

fun unify ((term1 as (Var n1)), term2) =
      if term1 = term2 then []
      else if occurs n1 term2 then failwith "unify"
      else [(n1,term2)]
  | unify (term1, Var n2) =
      if occurs n2 term1 then failwith "unify"
      else [(n2,term1)]
  | unify (Term(op1,sons1), Term(op2,sons2)) =
      if op1 = op2 then
        it_list2 (fn s => fn (t1,t2) => compsubst (unify(substitute s t1,
                                                         substitute s t2)) s)
                 [] sons1 sons2
      else failwith "unify"

(* We need to print terms with variables independently from input terms
  obtained by parsing. We give arbitrary names v1,v2,... to their variables. *)

val INFIXES = ["+","*"];

fun pretty_term (Var n) =
      (print_string "v"; print_num n)
  | pretty_term (Term (oper,sons)) =
      if mem oper INFIXES then
        case sons of
            [s1,s2] =>
              (pretty_close s1; print_string oper; pretty_close s2)
          | _ =>
              failwith "pretty_term : infix arity <> 2"
      else
       (print_string oper;
        case sons of
             []   => ()
          | t::lt =>(print_string "(";
                     pretty_term t;
                     app (fn t => (print_string ","; pretty_term t)) lt;
                     print_string ")"))
and pretty_close (M as Term(oper, _)) =
      if mem oper INFIXES then
        (print_string "("; pretty_term M; print_string ")")
      else pretty_term M
  | pretty_close M = pretty_term M

(****************** Equation manipulations *************)

(* standardizes an equation so its variables are 1,2,... *)

fun mk_rule M N =
  let val all_vars = union (vars M) (vars N);
      val (k,subst) =
        it_list (fn (i,sigma) => fn v => (i+1,(v,Var(i))::sigma))
               (1,[]) all_vars
  in (k-1, (substitute subst M, substitute subst N))
  end

(* checks that rules are numbered in sequence and returns their number *)
fun check_rules l = it_list (fn n => fn (k,_) =>
          if k=n+1 then k else failwith "Rule numbers not in sequence")
        0 l

fun pretty_rule (k,(n,(M,N))) =
 (print_num k; print_string " : ";
  pretty_term M; print_string " = "; pretty_term N;
  print_newline())

fun pretty_rules l = app pretty_rule l


(****************** Rewriting **************************)

(* Top-level rewriting. Let eq:L=R be an equation, M be a term such that L<=M.
   With sigma = matching L M, we define the image of M by eq as sigma(R) *)
fun reduce L M =
  substitute (matching L M)

(* A more efficient version of can (rewrite1 (L,R)) for R arbitrary *)
fun reducible L =
  let fun redrec M =
    (matching L M; true)
    handle Failure _ =>
      case M of Term(_,sons) => exists redrec sons
              |        _     => false
  in redrec
  end

(* mreduce : rules -> term -> term *)
fun mreduce rules M =
  let fun redex (_,(_,(L,R))) = reduce L M R in try_find redex rules end

(* One step of rewriting in leftmost-outermost strategy, with multiple rules *)
(* fails if no redex is found *)
(* mrewrite1 : rules -> term -> term *)
fun mrewrite1 rules =
  let fun rewrec M =
    (mreduce rules M) handle Failure _ =>
      let fun tryrec [] = failwith "mrewrite1"
            | tryrec (son::rest) =
                (rewrec son :: rest) handle Failure _ => son :: tryrec rest
      in case M of
          Term(f, sons) => Term(f, tryrec sons)
        | _ => failwith "mrewrite1"
      end
  in rewrec
  end

(* Iterating rewrite1. Returns a normal form. May loop forever *)
(* mrewrite_all : rules -> term -> term *)
fun mrewrite_all rules M =
  let fun rew_loop M =
    rew_loop(mrewrite1 rules M)  handle  Failure _ => M
  in rew_loop M
  end

(*
pretty_term (mrewrite_all Group_rules M where M,_=<<A*(I(B)*B)>>);;
==> A*U
*)


(************************ Recursive Path Ordering ****************************)

datatype ordering = Greater | Equal | NotGE;

fun ge_ord order pair = case order pair of NotGE => false | _ => true
and gt_ord order pair = case order pair of Greater => true | _ => false
and eq_ord order pair = case order pair of Equal => true | _ => false

fun rem_eq equiv =
  let fun remrec x [] = failwith "rem_eq"
        | remrec x (y::l) = if equiv (x,y) then l else y :: remrec x l
  in remrec
  end

fun diff_eq equiv (x,y) =
  let fun diffrec (p as ([],_)) = p
        | diffrec ((h::t), y) =
            diffrec (t,rem_eq equiv h y) handle Failure _ =>
              let val (x',y') = diffrec (t,y) in (h::x',y') end
  in if length x > length y then diffrec(y,x) else diffrec(x,y)
  end

(* multiset extension of order *)
fun mult_ext order (Term(_,sons1), Term(_,sons2)) =
      (case diff_eq (eq_ord order) (sons1,sons2) of
           ([],[]) => Equal
         | (l1,l2) =>
             if for_all (fn N => exists (fn M => order (M,N) = Greater) l1) l2
             then Greater else NotGE)
  | mult_ext order (_, _) = failwith "mult_ext"

(* lexicographic extension of order *)
fun lex_ext order ((M as Term(_,sons1)), (N as Term(_,sons2))) =
      let fun lexrec ([] , []) = Equal
            | lexrec ([] , _ ) = NotGE
            | lexrec ( _ , []) = Greater
            | lexrec (x1::l1, x2::l2) =
                case order (x1,x2) of
                  Greater => if for_all (fn N' => gt_ord order (M,N')) l2
                             then Greater else NotGE
                | Equal => lexrec (l1,l2)
                | NotGE => if exists (fn M' => ge_ord order (M',N)) l1
                           then Greater else NotGE
      in lexrec (sons1, sons2)
      end
  | lex_ext order _ = failwith "lex_ext"

(* recursive path ordering *)

fun rpo op_order ext =
  let fun rporec (M,N) =
    if M=N then Equal else
      case M of
          Var m => NotGE
        | Term(op1,sons1) =>
            case N of
                Var n =>
                  if occurs n M then Greater else NotGE
              | Term(op2,sons2) =>
                  case (op_order op1 op2) of
                      Greater =>
                        if for_all (fn N' => gt_ord rporec (M,N')) sons2
                        then Greater else NotGE
                    | Equal =>
                        ext rporec (M,N)
                    | NotGE =>
                        if exists (fn M' => ge_ord rporec (M',N)) sons1
                        then Greater else NotGE
  in rporec
  end

(****************** Critical pairs *********************)

(* All (u,sig) such that N/u (&var) unifies with M,
   with principal unifier sig *)

fun super M =
  let fun suprec (N as Term(_,sons)) =
      let fun collate (pairs,n) son =
                (pairs @ map (fn (u,sigma) => (n::u,sigma)) (suprec son), n+1);
          val insides =
                fst (it_list collate ([],1) sons)
      in ([], unify(M,N)) :: insides  handle Failure _ => insides
      end
    | suprec _ = []
  in suprec end

(* Ex :
let (M,_) = <<F(A,B)>>
and (N,_) = <<H(F(A,x),F(x,y))>> in super M N;;
==> [[1],[2,Term ("B",[])];                      x <- B
     [2],[2,Term ("A",[]); 1,Term ("B",[])]]     x <- A  y <- B
*)

(* All (u,sigma), u&[], such that N/u unifies with M *)
(* super_strict : term -> term -> (num list & subst) list *)

fun super_strict M (Term(_,sons)) =
        let fun collate (pairs,n) son =
          (pairs @ map (fn (u,sigma) => (n::u,sigma)) (super M son), n+1)
        in fst (it_list collate ([],1) sons) end
  | super_strict _ _ = []

(* Critical pairs of L1=R1 with L2=R2 *)
(* critical_pairs : term_pair -> term_pair -> term_pair list *)
fun critical_pairs (L1,R1) (L2,R2) =
  let fun mk_pair (u,sigma) =
     (substitute sigma (replace L2 u R1), substitute sigma R2) in
  map mk_pair (super L1 L2)
  end

(* Strict critical pairs of L1=R1 with L2=R2 *)
(* strict_critical_pairs : term_pair -> term_pair -> term_pair list *)
fun strict_critical_pairs (L1,R1) (L2,R2) =
  let fun mk_pair (u,sigma) =
    (substitute sigma (replace L2 u R1), substitute sigma R2) in
  map mk_pair (super_strict L1 L2)
  end

(* All critical pairs of eq1 with eq2 *)
fun mutual_critical_pairs eq1 eq2 =
  (strict_critical_pairs eq1 eq2) @ (critical_pairs eq2 eq1)

(* Renaming of variables *)

fun rename n (t1,t2) =
  let fun ren_rec (Var k) = Var(k+n)
        | ren_rec (Term(oper,sons)) = Term(oper, map ren_rec sons)
  in (ren_rec t1, ren_rec t2)
  end

(************************ Completion ******************************)

fun deletion_message (k,_) =
  (print_string "Rule ";print_num k; message " deleted")

(* Generate failure message *)
fun non_orientable (M,N) =
  (pretty_term M; print_string " = "; pretty_term N; print_newline())

(* Improved Knuth-Bendix completion procedure *)
(* kb_completion : (term_pair -> bool) -> num -> rules -> term_pair list -> (num & num) -> term_pair list -> rules *)
fun kb_completion greater =
  let fun kbrec n rules =
    let val normal_form = mrewrite_all rules;
        fun get_rule k = assoc k rules;
        fun process failures =
          let fun processf (k,l) =
            let fun processkl [] =
              if k<l then next_criticals (k+1,l) else
              if l<n then next_criticals (1,l+1) else
               (case failures of
                  [] => rules (* successful completion *)
                | _  => (message "Non-orientable equations :";
                         app non_orientable failures;
                         failwith "kb_completion"))
            | processkl ((M,N)::eqs) =
              let val M' = normal_form M;
                  val N' = normal_form N;
                  fun enter_rule(left,right) =
                    let val new_rule = (n+1, mk_rule left right) in
                     (pretty_rule new_rule;
                      let fun left_reducible (_,(_,(L,_))) = reducible left L;
                          val (redl,irredl) = partition left_reducible rules
                      in (app deletion_message redl;
                          let fun right_reduce (m,(_,(L,R))) =
                              (m,mk_rule L (mrewrite_all (new_rule::rules) R));
                              val irreds = map right_reduce irredl;
                              val eqs' = map (fn (_,(_,pair)) => pair) redl
                          in kbrec (n+1) (new_rule::irreds) [] (k,l)
                                   (eqs @ eqs' @ failures)
                          end)
                      end)
                    end
              in if M'=N' then processkl eqs else
                 if greater(M',N') then enter_rule(M',N') else
                 if greater(N',M') then enter_rule(N',M') else
                   process ((M',N')::failures) (k,l) eqs
              end
            in processkl
            end
          and next_criticals (k,l) =
            (let val (v,el) = get_rule l in
               if k=l then
                 processf (k,l) (strict_critical_pairs el (rename v el))
               else
                (let val (_,ek) = get_rule k in
                    processf (k,l) (mutual_critical_pairs el (rename v ek))
                 end
                 handle Failure "find" (*rule k deleted*) =>
                   next_criticals (k+1,l))
             end
             handle Failure "find" (*rule l deleted*) =>
                next_criticals (1,l+1))
          in processf
          end
    in process
    end
  in kbrec
  end

fun kb_complete greater complete_rules rules =
    let val n = check_rules complete_rules;
        val eqs = map (fn (_,(_,pair)) => pair) rules;
        val completed_rules =
               kb_completion greater n complete_rules [] (n,n) eqs
    in (message "Canonical set found :";
        pretty_rules (rev completed_rules);
        ())
    end

val Group_rules = [
  (1, (1, (Term("*", [Term("U",[]), Var 1]), Var 1))),
  (2, (1, (Term("*", [Term("I",[Var 1]), Var 1]), Term("U",[])))),
  (3, (3, (Term("*", [Term("*", [Var 1, Var 2]), Var 3]),
           Term("*", [Var 1, Term("*", [Var 2, Var 3])]))))];

val Geom_rules = [
 (1,(1,(Term ("*",[(Term ("U",[])), (Var 1)]),(Var 1)))),
 (2,(1,(Term ("*",[(Term ("I",[(Var 1)])), (Var 1)]),(Term ("U",[]))))),
 (3,(3,(Term ("*",[(Term ("*",[(Var 1), (Var 2)])), (Var 3)]),
  (Term ("*",[(Var 1), (Term ("*",[(Var 2), (Var 3)]))]))))),
 (4,(0,(Term ("*",[(Term ("A",[])), (Term ("B",[]))]),
  (Term ("*",[(Term ("B",[])), (Term ("A",[]))]))))),
 (5,(0,(Term ("*",[(Term ("C",[])), (Term ("C",[]))]),(Term ("U",[]))))),
 (6,(0,
  (Term
   ("*",
    [(Term ("C",[])),
     (Term ("*",[(Term ("A",[])), (Term ("I",[(Term ("C",[]))]))]))]),
  (Term ("I",[(Term ("A",[]))]))))),
 (7,(0,
  (Term
   ("*",
    [(Term ("C",[])),
     (Term ("*",[(Term ("B",[])), (Term ("I",[(Term ("C",[]))]))]))]),
  (Term ("B",[])))))
];

fun Group_rank "U" = 0
  | Group_rank "*" = 1
  | Group_rank "I" = 2
  | Group_rank "B" = 3
  | Group_rank "C" = 4
  | Group_rank "A" = 5

fun Group_precedence op1 op2 =
  let val r1 = Group_rank op1;
      val r2 = Group_rank op2
  in
    if r1 = r2 then Equal else
    if r1 > r2 then Greater else NotGE
  end

    val Group_order = rpo Group_precedence lex_ext

    fun greater pair = (case Group_order pair of Greater => true | _ => false)

    fun doit() = kb_complete greater [] Geom_rules

    val doit =
       fn size =>
       let
          fun loop n =
             if n = 0
                then ()
             else (doit();
                   loop(n-1))
       in loop size
       end

    fun testit _ = ()

  end (* Main *)

val foo = Main.doit 200;

(* Quit out correctly for interacive SMLs *)
val _ = OS.Process.exit(OS.Process.success);
