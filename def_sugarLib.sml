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
	  
fun mk_homo_clause fts n cons =
  let
      val (arg_types,ret_type) = type_of cons |> strip_fun
      val (f,typ) =
	  find_arg fts ret_type n
		   |> valOf |> (fn (s,t) => (mk_var(s,t),t))
      val fts_vars = map mk_var fts
      val consargs = map mk_var (zip (map (fst o dest_type) arg_types) arg_types)
      val consargs = variants consargs fts_vars
      val (tailtyps,rettyp) = strip_fun typ
      val argtyp = List.nth(tailtyps,n)
      val tailargs = map mk_var (zip (map type_name tailtyps) tailtyps)
      val tailargs = variants tailargs (fts_vars@consargs)
      val rets = consargs
		     |> map (fn v =>
				case find_arg fts (type_of v) n of
				    NONE => v
				  | SOME(s,t) =>
				    replace_after v n tailargs |>
						  List.foldl (mk_comb o swap) (mk_var(s,t))
				)
      val ntharg = List.foldl (mk_comb o swap) cons consargs
      val retconstyp = replace_type argtyp rettyp (type_of cons)
      val retcons =
	  if argtyp = rettyp then
	      cons
	  else
	      case (dest_const cons,dest_thy_type rettyp) of
		  ((s,_),t) => mk_thy_const {Name = s,Thy = (#Thy t), Ty = retconstyp}
  in
      mk_eq(	    
	  List.foldl (mk_comb o swap) f (replace_after ntharg n tailargs),
	  List.foldl (mk_comb o swap) retcons rets
      )
  end

fun clause_concat [] = raise Domain
  | clause_concat l =
    List.foldr mk_conj (List.last l) (List.take(l,length l - 1))

fun homomorphic_on fts n consvec =
  map (mk_homo_clause fts n) consvec
  |> clause_concat

fun setify_terms s = foldr (fn (v,x) => v :: filter (not o term_eq v) x) [] s;

fun mk_homomorphism fts n =
  map (curry (nth_arg o swap) n o snd) fts
  |> mlibUseful.setify
  |> concatMap TypeBase.constructors_of
  |> homomorphic_on fts n

fun to_quote a = list_of_singleton(ANTIQUOTE a)

fun ||> (tq,f) =
  to_quote(f(clause_concat(Defn.parse_quote tq))) : term quotation;

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

(* rearrange the clauses so that constructors in the function definition
   occur in the same order as in the datatype definition
 *)
fun reorder t =
  case find_cons_pattern t of
      SOME n =>
      let
	  val cls = defn_clauses t
	  fun reorder' cls [] = cls
	    | reorder' cls (c::cons) =
	      case List.partition (curry op = (SOME c) o clause_cons_of_var_pattern n) cls of
		  (cs,ncs) => cs @ reorder' ncs cons
	  val cons_order = map (clause_def_type n) cls
			       |> map mutrecs
			       |> mlibUseful.setify
			       |> List.concat
			       |> concatMap TypeBase.constructors_of
      in
	  reorder' cls cons_order |> clause_concat
      end
    | NONE => t

fun find_needed_mutrecs dc n matched nt =
  let
      val defined_cons = concatMap (fn ty => TypeBase.constructors_of ty |>
								map (specialise_cons ty))
			     matched_typs
			     |> mlibUseful.setify
      val unmatched_defined_cons = mlibUseful.subtract defined_cons matched
      val unmatched_args = unmatched_defined_cons |> map type_of |> map strip_fun |> concatMap fst
      val fst_arg_typs = map (clause_def_type n) dc |> mlibUseful.setify |> concatMap mutrecs |> mlibUseful.setify
      val needed_typs = mlibUseful.intersect fst_arg_typs unmatched_args
  in
      if length needed_typs > length nt then
	  find_needed_mutrecs dc n matched needed_typs
      else
	  needed_typs
  end

fun unmatched t =
  case find_cons_pattern t of
      SOME n =>
      let
	  val dc = defn_clauses t
	  val matched = List.mapPartial (clause_cons_of_var_pattern n) dc
	  val needed_typs = find_needed_mutrecs dc n matched matched_typs
	  val fst_arg_cons = concatMap (fn ty => TypeBase.constructors_of ty |>
								    map (specialise_cons ty))
				 needed_typs
				 |> mlibUseful.setify
      in
	  if exists (clause_var_pattern n) dc then
	      []
	  else
	      filter (fn c => exists (term_eq c) matched |> not) fst_arg_cons
      end
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



fun otherwise_homomorphic t =
  case find_cons_pattern t of
      SOME n =>
      (case unmatched t of
	  [] => t
	| l => reorder(mk_conj(t,
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
		       |> clause_concat
      val vs = def_vars clauses
      val substs = List.mapPartial (fn v =>
				       if is_const v then
					   SOME(v |-> mk_var(dest_const v))
				       else
					   NONE) vs
  in
      Term.subst substs clauses
  end

local
  val emptysubst:(term,term)Binarymap.dict = Binarymap.mkDict compare
  open Binarymap
  fun addb [] A = A
    | addb ({redex,residue}::t) (A,b) =
      addb t (insert(A,redex,residue), is_var redex andalso b)
in

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

end
