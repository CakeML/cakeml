(* From the SML/NJ benchmark suite. *)
(* knuth-bendix.sml
 *)

structure Main =
  struct

    val name = "Knuth-Bendix"

    fun length l = let
          fun j p = case p of
            (k, []) => k
          | (k, a::x) => j(k+1,x)
          in
            j(0,l)
          end

    fun append p = case p of
        ([], l) => l
      | (a::r, l) => a :: (append (r,l))

    fun rev l = let
          fun f p = case p of
            ([], h) => h
          | (a::r, h) => f(r, a::h)
          in
            f(l,[])
          end

    fun app f = let
          fun app_rec ls = case ls of
            [] => ()
          | (a::ls) => (f a; app_rec ls)
        in
          app_rec
        end

    fun map f = let
          fun map_rec ls = case ls of
            [] => []
          | (a::l) => f a :: map_rec l
          in
            map_rec
          end

(******* Quelques definitions du prelude CAML **************)

    exception Failure string;

    fun failwith s = raise(Failure s)

    fun fst (x,y) = x
    and snd (x,y) = y


fun it_list f =
  let fun it_rec a ls = case ls of
        [] => a
      | (b::l) => it_rec (f a b) l
  in it_rec
  end

fun it_list2 f =
  let fun it_rec  a   x y = case (x,y) of
          ([],[])    => a
        | (a1::l1,a2::l2) => it_rec (f a (a1,a2)) l1 l2
        | _ => failwith "it_list2"
  in it_rec
  end

fun exists p =
  let fun exists_rec ls = case ls of
          []  => False
        | (a::l) => (p a) orelse (exists_rec l)
  in exists_rec
  end

fun for_all p =
  let fun for_all_rec ls = case ls of
          []  => True
        | (a::l) => (p a) andalso (for_all_rec l)
  in for_all_rec
  end

fun rev_append   ls l  = case ls of
    [] => l
  | (x::l1) => rev_append l1 (x::l)

fun try_find f =
  let fun try_find_rec  ls = case ls of
          [] => failwith "try_find"
        | (a::l) => (f a) handle Failure _ => try_find_rec l
  in try_find_rec
  end

fun partition p =
  let fun part_rec ls = case ls of
          []   => ([],[])
        | (a::l) =>
            case part_rec l of (pos,neg) =>
              if p a then  ((a::pos), neg) else (pos, (a::neg))
  in part_rec
  end

(* 3- Les ensembles et les listes d'association *)

fun mem a =
  let fun mem_rec ls = case ls of
          [] => False
        | (b::l) => (a=b) orelse mem_rec l
  in mem_rec
  end

fun union l1 l2 =
  let fun union_rec ls = case ls of
          [] => l2
        | (a::l) =>
            if mem a l2 then union_rec l else a :: union_rec l
  in union_rec l1
  end

fun mem_assoc a =
  let fun mem_rec ls = case ls of
          [] => False
        | ((b,_)::l) => (a=b) orelse mem_rec l
  in mem_rec
  end

fun assoc a =
  let fun assoc_rec ls = case ls of
          [] => failwith "find"
        | ((b,d)::l) => if a=b then d else assoc_rec l
  in assoc_rec
  end

(* 4- Les sorties *)

(*fun print s = TextIO.output(TextIO.stdOut, s)*)
fun print _ = ()
val print_string = print
val print_num = fn x => print (Int.toString x)
fun print_newline () = print "\n";
fun message s = (print s; print "\n");

(* 5- Les ensembles *)

fun union l1 =
  let fun union_rec ls = case ls of
          [] => l1
        | (a::l) => if mem a l1 then union_rec l else a :: union_rec l
  in union_rec
  end

(****************** Term manipulations *****************)

datatype term = Var int | Term string (term list)

fun vars t = case t of
    (Var n) => [n]
  | (Term _ l) => vars_of_list l
and vars_of_list ls = case ls of
    [] => []
  | (t::r) => union (vars t) (vars_of_list r)

fun substitute subst =
  let fun subst_rec t = case t of
          (Term oper sons) => Term oper (map subst_rec sons)
        | ((Var n))     => (assoc n subst) handle Failure _ => t
  in subst_rec
  end

fun change f =
  let fun change_rec ls  n = case ls of
          (h::t)  => if n=1 then f h :: t
                            else h :: change_rec t (n-1)
        | _ => failwith "change"
  in change_rec
  end

(* Term replacement replace m u n => m[u<-n] *)
fun replace m u n =
  let fun reprec p = case p of
          (_, []) => n
        | (Term oper sons, (n::u)) =>
             Term oper (change (fn p => reprec(p,u)) sons n)
        | _ => failwith "replace"
  in reprec(m,u)
  end

(* matching = - : (term -> term -> subst) *)
fun matching term1 term2 =
  let fun match_rec subst p = case p of
          (Var v, m) =>
          if mem_assoc v subst then
            if m = assoc v subst then subst else failwith "matching"
          else
            (v,m) :: subst
        | (Term op1 sons1, Term op2 sons2) =>
          if op1 = op2 then it_list2 match_rec subst sons1 sons2
                       else failwith "matching"
        | _ => failwith "matching"
  in match_rec [] (term1,term2)
  end

(* A naive unification algorithm *)

fun compsubst subst1 subst2 =
  append (map (fn (v,t) => (v, substitute subst1 t)) subst2, subst1)

fun occurs n =
  let fun occur_rec t = case t of
          (Var m) => (m=n)
        | (Term _ sons) => exists occur_rec sons
  in occur_rec
  end

fun unify p = case p of
    (Var n1, term2) =>
      if Var n1 = term2 then []
      else if occurs n1 term2 then failwith "unify"
      else [(n1,term2)]
  | (term1, Var n2) =>
      if occurs n2 term1 then failwith "unify"
      else [(n2,term1)]
  | (Term op1 sons1, Term op2 sons2) =>
      if op1 = op2 then
        it_list2 (fn s => fn (t1,t2) => compsubst (unify(substitute s t1,
                                                         substitute s t2)) s)
                 [] sons1 sons2
      else failwith "unify"

(* We need to print terms with variables independently from input terms
  obtained by parsing. We give arbitrary names v1,v2,... to their variables. *)

val iNFIXES = ["+","*"];

fun pretty_term t = case t of
    (Var n) =>
      (print_string "v"; print_num n)
  | (Term oper sons) =>
      if mem oper iNFIXES then
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
and pretty_close m = case m of
    (Term oper _) =>
      if mem oper iNFIXES then
        (print_string "("; pretty_term m; print_string ")")
      else pretty_term m
  | _ => pretty_term m

(****************** Equation manipulations *************)

(* standardizes an equation so its variables are 1,2,... *)

fun mk_rule m n =
  let val all_vars = union (vars m) (vars n) in
  case
        it_list (fn p => case p of (i,sigma) => fn v => (i+1,(v,Var(i))::sigma))
               (1,[]) all_vars of
      (k,subst) =>
  (k-1, (substitute subst m, substitute subst n))
  end

(* checks that rules are numbered in sequence and returns their number *)
fun check_rules l = it_list (fn n => fn (k,_) =>
          if k=n+1 then k else failwith "Rule numbers not in sequence")
        0 l

fun pretty_rule (k,(n1,(m,n))) =
 (print_num k; print_string " : ";
  pretty_term m; print_string " = "; pretty_term n;
  print_newline())

fun pretty_rules l = app pretty_rule l

(****************** Rewriting **************************)

(* Top-level rewriting. let eq:l=r be an equation, m be a term such that l<=m.
   With sigma = matching l m, we define the image of m by eq as sigma(r) *)
fun reduce l m =
  substitute (matching l m)

(* A more efficient version of can (rewrite1 (l,r)) for r arbitrary *)
fun reducible l =
  let fun redrec m =
    (matching l m; True)
    handle Failure _ =>
      case m of Term _ sons => exists redrec sons
              |        _     => False
  in redrec
  end

(* mreduce : rules -> term -> term *)
fun mreduce rules m =
  let fun redex (u1,(u2,(l,r))) = reduce l m r in try_find redex rules end

(* One step of rewriting in leftmost-outermost strategy, with multiple rules *)
(* fails if no redex is found *)
(* mrewrite1 : rules -> term -> term *)
fun mrewrite1 rules =
  let fun rewrec m =
    (mreduce rules m) handle Failure _ =>
      let fun tryrec ls = case ls of
              [] => failwith "mrewrite1"
            | (son::rest) =>
                (rewrec son :: rest) handle Failure _ => son :: tryrec rest
      in case m of
          Term f sons => Term f (tryrec sons)
        | _ => failwith "mrewrite1"
      end
  in rewrec
  end

(* Iterating rewrite1. returns a normal form. may loop forever *)
(* mrewrite_all : rules -> term -> term *)
fun mrewrite_all rules m =
  let fun rew_loop m =
    rew_loop(mrewrite1 rules m)  handle  Failure _ => m
  in rew_loop m
  end

(*
pretty_term (mrewrite_all Group_rules m where m,_=<<A*(I(B)*B)>>);;
==> A*U
*)

(************************ Recursive Path Ordering ****************************)

datatype ordering = Greater | Equal | NotGE;

fun ge_ord order pair = case order pair of NotGE => False | _ => True
and gt_ord order pair = case order pair of Greater => True | _ => False
and eq_ord order pair = case order pair of Equal => True | _ => False

fun rem_eq equiv =
  let fun remrec x ls = case ls of
          [] => failwith "rem_eq"
        | (y::l) => if equiv (x,y) then l else y :: remrec x l
  in remrec
  end

fun diff_eq equiv (x,y) =
  let fun diffrec p = case p of
          ([],_) => p
        | ((h::t), y) =>
            diffrec (t,rem_eq equiv h y) handle Failure _ =>
              case diffrec (t,y) of (x',y') => (h::x',y')
  in if length x > length y then diffrec(y,x) else diffrec(x,y)
  end

(* multiset extension of order *)
fun mult_ext order p = case p of
  (Term u1 sons1, Term u2 sons2) =>
      (case diff_eq (eq_ord order) (sons1,sons2) of
           ([],[]) => Equal
         | (l1,l2) =>
             if for_all (fn n => exists (fn m => order (m,n) = Greater) l1) l2
             then Greater else NotGE)
  | (u1, u2) => failwith "mult_ext"

(* lexicographic extension of order *)
fun lex_ext order (m,n) = case (m,n) of
  (Term u1 sons1, Term u2 sons2) =>
      let fun lexrec p = case p of
              ([] , []) => Equal
            | ([] , _ ) => NotGE
            | ( _ , []) => Greater
            | (x1::l1, x2::l2) =>
                case order (x1,x2) of
                  Greater => if for_all (fn n' => gt_ord order (m,n')) l2
                             then Greater else NotGE
                | Equal => lexrec (l1,l2)
                | NotGE => if exists (fn m' => ge_ord order (m',n)) l1
                           then Greater else NotGE
      in lexrec (sons1, sons2)
      end
  | _ => failwith "lex_ext"

(* recursive path ordering *)

fun rpo op_order ext =
  let fun rporec (m,n) =
    if m=n then Equal else
      case m of
          Var m => NotGE
        | Term op1 sons1 =>
            case n of
                Var n =>
                  if occurs n m then Greater else NotGE
              | Term op2 sons2 =>
                  case (op_order op1 op2) of
                      Greater =>
                        if for_all (fn n' => gt_ord rporec (m,n')) sons2
                        then Greater else NotGE
                    | Equal =>
                        ext rporec (m,n)
                    | NotGE =>
                        if exists (fn m' => ge_ord rporec (m',n)) sons1
                        then Greater else NotGE
  in rporec
  end

(****************** Critical pairs *********************)

(* All (u,sig) such that N/u (&var) unifies with M,
   with principal unifier sig *)

fun super m =
  let fun suprec n = case n of
      Term _ sons =>
      let fun collate (pairs,n) son =
                (append (pairs,map (fn (u,sigma) => (n::u,sigma)) (suprec son)), n+1);
          val insides =
                fst (it_list collate ([],1) sons)
      in ([], unify(m,n)) :: insides  handle Failure _ => insides
      end
    | _ => []
  in suprec end

(* Ex :
let (m,_) = <<F(A,B)>>
and (n,_) = <<H(F(A,x),F(x,y))>> in super m n;;
==> [[1],[2,Term "B" []];                      x <- B
     [2],[2,Term "A" []; 1,Term "B" []]]     x <- A  y <- B
*)

(* All (u,sigma), u&[], such that n/u unifies with m *)
(* super_strict : term -> term -> (num list & subst) list *)

fun super_strict m t = case t of
  (Term _ sons) =>
        let fun collate (pairs,n) son =
          (append (pairs,map (fn (u,sigma) => (n::u,sigma)) (super m son)), n+1)
        in fst (it_list collate ([],1) sons) end
  | _ => []

(* Critical pairs of l1=r1 with l2=r2 *)
(* critical_pairs : term_pair -> term_pair -> term_pair list *)
fun critical_pairs (l1,r1) (l2,r2) =
  let fun mk_pair (u,sigma) =
     (substitute sigma (replace l2 u r1), substitute sigma r2) in
  map mk_pair (super l1 l2)
  end

(* Strict critical pairs of l1=r1 with l2=r2 *)
(* strict_critical_pairs : term_pair -> term_pair -> term_pair list *)
fun strict_critical_pairs (l1,r1) (l2,r2) =
  let fun mk_pair (u,sigma) =
    (substitute sigma (replace l2 u r1), substitute sigma r2) in
  map mk_pair (super_strict l1 l2)
  end

(* All critical pairs of eq1 with eq2 *)
fun mutual_critical_pairs eq1 eq2 =
  append ((strict_critical_pairs eq1 eq2),(critical_pairs eq2 eq1))

(* renaming of variables *)

fun rename n (t1,t2) =
  let fun ren_rec t = case t of
          (Var k) => Var(k+n)
        | (Term oper sons) => Term oper (map ren_rec sons)
  in (ren_rec t1, ren_rec t2)
  end

(************************ Completion ******************************)

fun deletion_message (k,_) =
  (print_string "Rule ";print_num k; message " deleted")

(* Generate failure message *)
fun non_orientable (m,n) =
  (pretty_term m; print_string " = "; pretty_term n; print_newline())

(* Improved Knuth-Bendix completion procedure *)
(* kb_completion : (term_pair -> bool) -> num -> rules -> term_pair list -> (num & num) -> term_pair list -> rules *)
fun kb_completion greater =
  let fun kbrec nn rules =
    let val normal_form = mrewrite_all rules;
        fun get_rule k = assoc k rules;
        fun process failures =
          let fun processf (k,l) =
                        let fun processkl ls = case ls of
              [] =>
              if k<l then next_criticals (k+1,l) else
              if l<nn then next_criticals (1,l+1) else
               (case failures of
                  [] => rules (* successful completion *)
                | _  => (message "non-orientable equations :";
                         app non_orientable failures;
                         failwith "kb_completion"))
              | ((m,n)::eqs) =>
              let val m' = normal_form m;
                  val n' = normal_form n;
                  fun enter_rule(left,right) =
                    let val new_rule = (nn+1, mk_rule left right) in
                    (pretty_rule new_rule;
                      let fun left_reducible (u1,(u2,(ll,u3))) = reducible left ll;
                      in
                        case partition left_reducible rules of (redl,irredl) =>
                         (app deletion_message redl;
                          let fun right_reduce (m,(_,(ll,rr))) =
                              (m,mk_rule ll (mrewrite_all (new_rule::rules) rr));
                              val irreds = map right_reduce irredl;
                              val eqs' = map (fn (u1,(u2,pair)) => pair) redl
                          in kbrec (nn+1) (new_rule::irreds) [] (k,l)
                                   (append (eqs, append(eqs',failures)))
                          end)
                      end)
                    end
              in if m'=n' then processkl eqs else
                 if greater(m',n') then enter_rule(m',n') else
                 if greater(n',m') then enter_rule(n',m') else
                   process ((m',n')::failures) (k,l) eqs
              end
            in processkl
            end

          and next_criticals (k,l) =
            ((case get_rule l of (v,el) =>
               if k=l then
                 processf (k,l) (strict_critical_pairs el (rename v el))
               else
                ((case get_rule k of (_,ek) =>
                    processf (k,l) (mutual_critical_pairs el (rename v ek)))
                 handle Failure "find" (*rule k deleted*) =>
                   next_criticals (k+1,l)))
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
        val eqs = map (fn (u1,(u2,pair)) => pair) rules;
        val completed_rules =
               kb_completion greater n complete_rules [] (n,n) eqs
    in (message "Canonical set found :";
        pretty_rules (rev completed_rules);
        ())
    end

val group_rules = [
  (1, (1, (Term "*" ([Term "U"([]), Var 1]), Var 1))),
  (2, (1, (Term "*" ([Term "I"([Var 1]), Var 1]), Term "U" ([])))),
  (3, (3, (Term "*" ([Term "*"( [Var 1, Var 2]), Var 3]),
           Term "*" ([Var 1, Term"*" ([Var 2, Var 3])]))))];

val geom_rules = [
 (1,(1,(Term "*"([(Term "U"([])), (Var 1)]),(Var 1)))),
 (2,(1,(Term "*"([(Term "I"([(Var 1)])), (Var 1)]),(Term "U"([]))))),
 (3,(3,(Term "*"([(Term "*"([(Var 1), (Var 2)])), (Var 3)]),
  (Term "*"([(Var 1), (Term "*"([(Var 2), (Var 3)]))]))))),
 (4,(0,(Term "*"([(Term "A"([])), (Term "B"([]))]),
  (Term "*"([(Term "B"([])), (Term "A"([]))]))))),
 (5,(0,(Term "*"([(Term "C"([])), (Term "C"([]))]),(Term "U"([]))))),
 (6,(0,
  (Term
    "*"
    ([(Term "C"([])),
     (Term "*"([(Term "A"([])), (Term "I"([(Term "C"([]))]))]))]),
  (Term "I"([(Term "A"([]))]))))),
 (7,(0,
  (Term
   "*"
    ([(Term "C"([])),
     (Term "*"([(Term "B"([])), (Term "I"([(Term "C"([]))]))]))]),
  (Term "B"([])))))
];

fun group_rank s = case s of
    "U" => 0
  | "*" => 1
  | "I" => 2
  | "B" => 3
  | "C" => 4
  | "A" => 5

fun group_precedence op1 op2 =
  let val r1 = group_rank op1;
      val r2 = group_rank op2
  in
    if r1 = r2 then Equal else
    if r1 > r2 then Greater else NotGE
  end

    val group_order = rpo group_precedence lex_ext

    fun greater pair = (case group_order pair of Greater => True | _ => False)

    fun doit() = kb_complete greater [] geom_rules

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
