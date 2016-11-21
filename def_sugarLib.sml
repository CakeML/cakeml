structure def_sugarLib :> def_sugarLib = struct

open HolKernel boolLib bossLib lcsymtacs

fun concatMap f = foldr (fn(a,b) => f a @ b) []

fun variants [] l = []
  | variants (f::r) l =
    let
	val v = variant l f
    in
	v :: variants r (v::l)
    end

(* differs from FinalType.type_subst in that the redex need not be a type variable *)
fun replace_type redex residue typ =
  if typ = redex then
      residue
  else if is_type typ then
      case dest_thy_type typ of
	  ti => mk_thy_type {Thy = #Thy ti,
			     Tyop = #Tyop ti,
			     Args = map (replace_type redex residue) (#Args ti)}
  else
      typ

local
  val emptysubst:(term,term)Binarymap.dict = Binarymap.mkDict compare
  open Binarymap
  fun addb [] A = A
    | addb ({redex,residue}::t) (A,b) =
      addb t (insert(A,redex,residue), is_var redex andalso b)
in

fun all_constructors t =
  case dest_term t of
      COMB(rator,rand) => all_constructors rator @ all_constructors rand
    | LAMB(x,body) => all_constructors x @ all_constructors body
    | CONST _ => filter TypeBase.is_constructor [t]
    | _ => []

fun term_subst theta =
  let
      val (fmap,b) = addb theta (emptysubst, true)
      val fv = concatMap (fn {redex,residue} => [redex,residue]) theta |>
		   concatMap free_vars
      fun subst tm =
	case peek(fmap,tm) of
	    SOME residue => residue
	  | NONE =>
	    (case dest_term tm of
		 COMB(rator,rand) => mk_comb(subst rator, subst rand)
	       | LAMB(x,body) =>
		 let val x' = variant (fv @ (mlibUseful.subtract (free_vars body) [x])) x
		 in
		     if term_eq x x' then
			 mk_abs(x,subst body)
		     else
			 mk_abs(x',subst (Term.subst [x |-> x'] body))
		 end
	       | _ => tm
	    )
  in
      subst
  end
end

(* nth_arg(t,n) returns the n:th argument type of the
   function type t, starting from 0.
   Fails if t is not a function type with at least (n+1)
   curried arguments.

   Ex: nth_arg(``:num -> bool -> num``,1) = ``:bool``
 *)	  
fun nth_arg(t,n) = List.nth(fst(strip_fun t),n)

fun first_arg t = nth_arg(t,0)

(* find_arg fun_typs arg_typ n
   returns NONE if no function type in fun_typ has
   arg_typ as its n:th argument type.
   returns SOME(v,t) if (v,t) is the first element
   of fun_typs such that arg_typ is the n:th argument
   of t.
 *)
fun find_arg fun_typs arg_typ n =
  List.find (curry op = arg_typ o curry (nth_arg o swap) n o snd) fun_typs

fun type_name t =
  if is_type t then
      fst(dest_type t)
  else
      let
	  val s = dest_vartype t
      in
	  String.substring(s,1,size s - 1)
      end

fun insert_after e 0 l = e::l
  | insert_after _ _ [] = raise Domain
  | insert_after e n (f::r) =
    f::insert_after e (n-1) r

fun replace_after e 0 (f::r) = e::r
  | replace_after _ _ [] = raise Domain
  | replace_after e n (f::r) =
    f::replace_after e (n-1) r

fun return_type t = snd(strip_fun t)
	  
fun mk_homo_clause fts n cons =
  let
      val ret_type = type_of cons |> return_type
      val (f,typ) =
	  find_arg fts ret_type n
		   |> valOf |> (fn (s,t) => (mk_var(s,t),t))
      val fts_vars = map mk_var fts
      val consargs = free_vars cons
      val consargs' = variants consargs fts_vars
      val (tailtyps,rettyp) = strip_fun typ
      val argtyp = List.nth(tailtyps,n)
      val tailargs = map mk_var (zip (map type_name tailtyps) tailtyps)
      val tailargs = variants tailargs (fts_vars@consargs)
      val conssubst = ListPair.map (fn (v,v') =>
				       case find_arg fts (type_of v) n of
					   NONE => v|->v'
					 | SOME(s,t) => v|->
							 (replace_after v' n tailargs |>
									List.foldl (mk_comb o swap) (mk_var(s,t))))
				   (consargs,consargs')
      val ntharg = Term.subst (ListPair.map (op |->) (consargs,consargs')) cons
      val arg_types = map (fn (_,t) => nth_arg(t,n)) fts
      val retconsubst =
	  all_constructors cons |>
			   concatMap
			   (fn c =>
			       let val ctyp = type_of c |> strip_fun |> snd
			       in
				   case List.find (curry op = ctyp o fst) (zip arg_types fts) of
				       NONE => []
				     | SOME(rettyp,(_,ft)) =>
				       (case (dest_const c,dest_thy_type(return_type ft)) of
					    ((s,_),t) => [c |-> mk_thy_const {Name = s,
									      Thy = (#Thy t),
									      Ty = replace_type ctyp (mk_thy_type t) (type_of c)}])
			       end)
  in
      mk_eq(
	  List.foldl (mk_comb o swap) f (replace_after ntharg n tailargs),
	  term_subst (conssubst@retconsubst) cons
      )
  end

fun homomorphic_on fts n consvec =
  map (mk_homo_clause fts n) consvec
  |> list_mk_conj

fun setify_terms s = foldr (fn (v,x) => v :: filter (not o term_eq v) x) [] s;

fun to_quote a = [ANTIQUOTE a];

fun ||> (tq,f) =
  to_quote(f(fst(Defn.parse_absyn(Parse.Absyn tq)))) : term quotation;

fun defn_clauses t =
  if is_conj t then
      case dest_conj t of
	  (t1,t2) => defn_clauses t1 @ defn_clauses t2
  else
      [t]

fun strip_comb t =
  if is_comb t then
      case dest_comb t of
	  (t1,t2) => (strip_comb t1)@[t2]
  else
      [t]

fun clause_fun t =
  hd(dest_eq t |> fst |> strip_comb)

fun clause_nth_arg n t =
  List.nth(dest_eq t |> fst |> strip_comb,
	   n+1)

fun clause_var_pattern n t =
  is_var(clause_nth_arg n t)

fun clause_find_cons_pattern c =
  let
      val arity = clause_fun c |> type_of |> strip_fun |> fst |> length
      val pats = List.tabulate(arity,
			fn n => (n,Option.filter (not o is_var) (clause_nth_arg n c)))
  in
      case List.filter (isSome o snd) pats of
	  [(n,_)] => SOME n
	| [] => NONE
	| _ => raise ERR "clause_find_cons_pattern" "Non-variable patterns occuring in multiple arguments"
  end

fun find_cons_pattern def =
  case defn_clauses def |>
		   map clause_find_cons_pattern |>
		   mlibUseful.setify |>
		   filter isSome of
      [SOME n] => SOME n
    | [] => NONE
    | _ => raise ERR "find_cons_pattern"
		 "Clauses with recursion over different arguments not supported"

fun cons_of_var_pattern pat =
  if is_comb pat then
      case strip_comb pat of
	  x::xs =>
	  if is_const x andalso all is_var xs then
	      true
	  else
	      false
	| _ => false (*TODO: error messages *)
  else if is_const pat then
      true
  else
      false

fun clause_cons_of_var_pattern n t =
  let
      val c = clause_nth_arg n t
  in
      if is_comb c then
	  case strip_comb c of
	      x::xs =>
	      if is_const x andalso all is_var xs then
		  SOME x
	      else
		  NONE
	    | _ => NONE (*TODO: error messages *)
      else if is_const c then
	  SOME c
      else
	  NONE
  end

fun clause_def_type n c =
  clause_nth_arg n c |> type_of

fun def_vars t =
  defn_clauses t
  |> map clause_fun
  |> setify_terms

fun def_names t = def_vars t |> map (fst o dest_var)

fun def_types t = def_vars t |> map (snd o dest_var)

fun specialise_cons typ cons =
  let val cons_typ = type_of cons |> strip_fun |> snd
  in
      Term.inst (match_type cons_typ typ) cons
  end

fun typ_same_cons t t' =
  case (dest_thy_type t, dest_thy_type t') of
      ({Args=_,Thy=thy,Tyop=s},{Args=_,Thy=thy',Tyop=s'}) => s = s' andalso thy = thy'      
      
fun reinstantiate t tys =
  if List.exists (curry op = t) tys then
      tys
  else
      case dest_thy_type t of
	  {Args=l,...} =>
	  case Option.map dest_type (List.find (typ_same_cons t) tys) of
	      NONE => raise ERR "reinstantiate"
			    "Failed to find generalisation of original type"
	    | SOME(_,l') => map (type_subst
				     (ListPair.map (op |->) (l',l)))
				tys

(* returns the types that t is mutually recursively defined together with (including t)
 *)
fun mutrecs t = 
  TypeBase.induction_of t |> dest_thm |> rpt strip_tac
  |> fst |> map snd |> map rand |> map type_of |> reinstantiate t

(* rearrange the clauses so that:
   a) defined functions occur in the order of the argument fo
   b) constructors in the function definition
      occur in the same order as in the datatype definition (TODO: handle nested patterns)
 *)
fun reorder fo t =
  case find_cons_pattern t of
      SOME n =>
      let
	  val cls = defn_clauses t
	  fun reorder'' [] cls = cls
	    | reorder'' (f::fos) cls =
	      case List.partition (term_eq f o clause_fun) cls of
		  (cs,ncs) => cs @ reorder'' fos ncs
	  fun reorder' cls [] = cls
	    | reorder' cls (c::cons) =
	      case List.partition (curry (getOpt o swap) false o Option.map (term_eq c) o clause_cons_of_var_pattern n) cls of
		  (cs,ncs) => cs @ reorder' ncs cons
	  val cons_order = map (clause_def_type n) cls
			       |> map mutrecs
			       |> mlibUseful.setify
			       |> List.concat
			       |> concatMap TypeBase.constructors_of
      in
	  reorder' cls cons_order
		   |> reorder'' fo
		   |> list_mk_conj
      end
    | NONE => t

fun find_needed_mutrecs matched nt =
  let
      val defined_cons = concatMap (fn ty => TypeBase.constructors_of ty |>
								map (specialise_cons ty))
			     nt
			     |> mlibUseful.setify
      val unmatched_defined_cons = mlibUseful.subtract defined_cons (map (hd o strip_comb) matched)
      val unmatched_cons_typs = map (snd o strip_fun o type_of) unmatched_defined_cons
      val unmatched_args = concatMap (fst o strip_fun o type_of) unmatched_defined_cons
      val fst_arg_typs = map type_of matched |> mlibUseful.setify |> concatMap mutrecs |> mlibUseful.setify
      val needed_typs = mlibUseful.intersect fst_arg_typs
					     (mlibUseful.union unmatched_args unmatched_cons_typs)
  in
      if length needed_typs > length nt then
	  find_needed_mutrecs matched needed_typs
      else
	  needed_typs
  end

fun comb_nth_arg n t =
  List.nth(strip_comb t,n+1)

fun clause_nth_arg n c =
  comb_nth_arg n (fst(dest_eq c))

fun saturate avoid cons =
  case strip_fun(type_of cons) of
      (args,c) =>
      List.foldl (mk_comb o swap) cons (variants (map (fn t => mk_var(type_name t, t)) args) avoid)
      | _ => raise Domain

fun pat_eq p p' =
  case (dest_term p,dest_term p') of
      (COMB(p1,p2),COMB(p3,p4)) => pat_eq p1 p3 andalso pat_eq p2 p4
    | (VAR _, VAR _) => true
    | (CONST c, CONST c') => c = c'
    | _ => false (* probably no need to handle abstractions *)

fun pat_subpat p p' =
  case (dest_term p,dest_term p') of
      (COMB(p1,p2),COMB(p3,p4)) => pat_subpat p1 p3 andalso pat_subpat p2 p4
    | (_, VAR _) => true
    | (CONST c, CONST c') => c = c'
    | _ => false (* probably no need to handle abstractions *)

fun setify_pat s = foldr (fn (v,x) => v :: filter (not o pat_eq v) x) [] s;

local
fun put f (e,[]) = [[e]]
  | put f (e,((e'::x)::xs)) =
    if f e e' then
	(e::e'::x)::xs
    else
	(e'::x)::(put f (e,xs))
  | put _ (_,[]::xs) = raise Domain
in
fun buckets f =
  foldr (put f) []
end

fun same_cons t t' =
  term_eq (hd(strip_comb t)) (hd(strip_comb t'))

fun transpose [] = []
  | transpose (l) =
    if exists null l then
	[]
    else
	(map hd l) :: transpose(map tl l)

fun combinations [] = [[]]
  | combinations (f::r) =
    concatMap (fn x => map (curry op :: x) (combinations r)) f

(* (term * term list) list => (term * term list list) *)
fun categorise' [] = raise Domain
  | categorise' [(t,tl)] = (t,[tl])
  | categorise' ((_,tl)::tll) =
    let val (t,tll') = categorise' tll
    in
	(t,tl::tll')
    end

(* (term * term list) list list => (term * term list list) list *)
fun categorise l = map categorise' l

fun arg_cons t =
  concatMap (fn ty => TypeBase.constructors_of ty |>
					       map (specialise_cons ty))
	    t
	    |> mlibUseful.setify
	    |> map (saturate []) (*fixme: avoid fun names *)

fun pat_mem x = List.exists (pat_eq x);

fun pat_subpat_mem x = List.exists (pat_subpat x);

fun pat_subpat_rmem x y = List.exists (fn z => pat_subpat z x) y; 

fun pat_subtract s t = foldl (fn (v,x) => if pat_mem v t then x else v::x) [] (rev s);

fun pat_subpat_subtract s t = foldl (fn (v,x) => if pat_subpat_mem v t then x else v::x) [] (rev s);

fun pat_subpat_setify s = foldl (fn (v,x) => if pat_subpat_rmem v x then x else v::x) [] s;

datatype pattern = PATTERN of (term * pattern list) list

fun pat_unfold (PATTERN cv) cons =
  let val cv' = strip_comb cons
  in
      case partition (term_eq (hd cv') o fst) cv of
	  ([],cv) =>
	  (case dest_term cons of
	       VAR _ => PATTERN((cons,[])::cv)
	     | CONST _ => PATTERN ((hd cv',map (pat_unfold (PATTERN [])) (tl cv'))::cv)
	     | COMB _ => PATTERN((hd cv', map (pat_unfold (PATTERN [])) (tl cv'))::cv))
	| ([(c,pv)],cv) =>
	  (case dest_term cons of
	       VAR _ => PATTERN cv
	     | _ => PATTERN ((c,ListPair.map (uncurry pat_unfold) (pv,tl cv'))::cv))
  end

fun pat_complete (PATTERN []) = PATTERN []
  | pat_complete (PATTERN ((c,p)::p')) =
    let
	val (PATTERN p'') = pat_complete (PATTERN p')
    in
	if is_var c then
	    PATTERN((c,p)::p'')
	else
	    let
		val rt = return_type(type_of c)
		val conses = rt |> TypeBase.constructors_of |> map (specialise_cons rt)
		val newconses = filter (fn c' => not (exists (term_eq c' o fst) ((c,p)::p'))) conses
				       |> map (saturate [])
	    in
		List.foldr (fn (c,p) =>  pat_unfold p c)
			   (PATTERN((c,map pat_complete p) :: p''))
			   newconses
	    end
    end

fun pat_to_list (PATTERN []) = []
  | pat_to_list (PATTERN((c,[])::p')) =
    c :: pat_to_list(PATTERN p')
  | pat_to_list (PATTERN((c,p)::p')) =
    map (List.foldl (mk_comb o swap) c) (map pat_to_list p |> combinations)
    @ pat_to_list(PATTERN p')

fun rename avoid t =
  case dest_term t of
      COMB(rator,rand) =>
      let
	  val rr = rename avoid rator
      in
	  mk_comb(rr,rename (avoid @ free_vars rr) rand)
      end
    | VAR _ => variant avoid t
    | _ => t

fun unmatched' matched =
  let
      val matched_typs = map type_of matched |> mlibUseful.setify
      val needed_typs =
	  mlibUseful.subtract (find_needed_mutrecs matched matched_typs)
			      matched_typs
      val fst_arg_cons = arg_cons needed_typs
      val satpats = List.foldr (fn (x,y) => pat_unfold y x) (PATTERN []) (matched@fst_arg_cons)
			       |> pat_complete
			       |> pat_to_list
			       |> map (rename [])
  in
      pat_subpat_subtract satpats matched |> pat_subpat_setify
  end
	  
fun unmatched t =
  case find_cons_pattern t of
      SOME n =>
      unmatched' (map (clause_nth_arg n) (defn_clauses t))
      | NONE => [] (* TODO: mutrecs? *)

fun invent_fun_names fts _ [] fvt = fts
  | invent_fun_names (fts as (s,t):: _) n (c::cs) fvt =
    let
	val ctyp = type_of c |> strip_fun |> snd
    in
	case find_arg fts ctyp n of
	    SOME _ => invent_fun_names fts n cs fvt
	  | NONE =>
	    let
		val ot = nth_arg(t,n)
		val ftyp = replace_type ot ctyp t
		val v = s ^ "_" ^ type_name ctyp
		val new_fts =
		    case List.find (fn v => type_of v = ftyp) (concatMap free_vars fvt) of
			SOME v => fts @ [variant (map mk_var fts) v |> dest_var]
		      | NONE => fts @ [variant (fvt@map mk_var fts) (mk_var(v,ftyp)) |> dest_var]
	    in
		invent_fun_names new_fts n cs fvt
	    end
    end
  | invent_fun_names [] _ _ _ = raise Domain

fun fun_order t =
  defn_clauses t |> map clause_fun |> setify_terms

fun otherwise_homomorphic t =
  case find_cons_pattern t of
      SOME n =>
      (case unmatched t of
	  [] => t
	| l => reorder (fun_order t) (mk_conj(t,
			       homomorphic_on (invent_fun_names (zip (def_names t)
								     (def_types t))
								n l (free_vars t))
					      n l)))
      | NONE => t (*todo: mutrecs?*)

(* Given a function definition, reconstruct a term
   from which the definition could have been constructed
 *)		  
fun def_to_term thm =
  let
      val clauses = dest_thm thm
		       |> rpt strip_tac
		       |> fst
		       |> map snd
		       |> list_mk_conj
      val vs = def_vars clauses
      val substs = List.mapPartial (fn v =>
				       if is_const v then
					   SOME(v |-> mk_var(dest_const v))
				       else
					   NONE) vs
  in
      Term.subst substs clauses
  end


end
