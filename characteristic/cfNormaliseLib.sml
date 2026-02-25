(*
  Automation that normalises a CakeML program. In particular, this
  means turning it into A-normal form.
*)
structure cfNormaliseLib :> cfNormaliseLib = struct

open preamble
open astSyntax

val ERR = mk_HOL_ERR "cfNormaliseLib";

(* Normalisation pass.

   [normalise_prog] (and friends) implement a preprocessing pass on the
   CakeML program to be fed to [cf]. It turns a CakeML program into
   A-normal form; [cf] then assumes the input program is in A-normal
   form. [cf] evaluates to [F] for programs not in A-normal form.

   At the moment, this normalisation pass is unverified: formally, the
   specification proved using CF is a specification for the
   _normalised_ program, not the original one. Eventually it would be
   nice to have a proof that normalisation preserves the semantics of
   its input in some way.

   This normalisation pass is currently implemented directly in ML. It
   used to be implemented as a HOL function, but for performance
   reasons, it has been re-implemented to what follows. The remains of
   the old normalisation function can be found at the end of
   [cfNormaliseScript.sml].

   The implementation follows the structure of the CFML one, in
   generator/normalize.ml in the CFML sources.
*)

(* We first strip line & type annotations *)

fun dest_triple tm = let
  val (x, yz) = pairLib.dest_pair tm
  val (y, z) = pairLib.dest_pair yz
in (x, y, z) end

fun mk_triple (t1, t2, t3) =
  pairLib.mk_pair (t1, pairLib.mk_pair (t2, t3))

fun strip_annot_pat p =
  if is_Pvar p
     orelse is_Plit p
     orelse p ~~ Pany
  then
      p
  else if is_Pcon p then
    let val (c, xs) = dest_Pcon p in
    mk_Pcon (c, strip_annot_pats xs) end
  else if is_Pref p then
    let val p' = dest_Pref p in
    mk_Pref (strip_annot_pats p') end
  else if is_Ptannot p then
    let val (p', _) = dest_Ptannot p in
    strip_annot_pat p' end
  else raise (ERR "unknown constructor" "strip_annot_pat")

and strip_annot_pats tm = let
  val (ps, ty) = listSyntax.dest_list tm
  val ps' = map strip_annot_pat ps
in listSyntax.mk_list (ps', ty) end

fun strip_annot_exp tm =
  if is_Raise tm then mk_Raise (strip_annot_exp (dest_Raise tm))
  else if is_Handle tm then
    let val (e, pes) = dest_Handle tm in
    mk_Handle (strip_annot_exp e, strip_annot_pes pes) end
  else if is_Lit tm orelse is_Var tm then tm
  else if is_Con tm then
    let val (cn, es) = dest_Con tm in
    mk_Con (cn, strip_annot_exps es) end
  else if is_Fun tm then
    let val (x, e) = dest_Fun tm in
    mk_Fun (x, strip_annot_exp e) end
  else if is_App tm then
    let val (op_, es) = dest_App tm in
    mk_App (op_, strip_annot_exps es) end
  else if is_Log tm then
    let val (lop, e1, e2) = dest_Log tm in
    mk_Log (lop, strip_annot_exp e1, strip_annot_exp e2) end
  else if is_If tm then
    let val (e1, e2, e3) = dest_If tm in
    mk_If (strip_annot_exp e1, strip_annot_exp e2, strip_annot_exp e3) end
  else if is_Mat tm then
    let val (e, pes) = dest_Mat tm in
    mk_Mat (strip_annot_exp e, strip_annot_pes pes) end
  else if is_Let tm then
    let val (xo, e1, e2) = dest_Let tm in
    mk_Let (xo, strip_annot_exp e1, strip_annot_exp e2) end
  else if is_Letrec tm then
    let val (funs, e) = dest_Letrec tm in
    mk_Letrec (strip_annot_funs funs, strip_annot_exp e) end
  else if is_Tannot tm then
    let val (e, _) = dest_Tannot tm in
    strip_annot_exp e end
  else if is_Lannot tm then
    let val (e, _) = dest_Lannot tm in
    strip_annot_exp e end
  else raise (ERR "unknown constructor" "strip_annot_exp")

and strip_annot_exps tm = let
  val (es, ty) = listSyntax.dest_list tm
  val es' = map strip_annot_exp es
in listSyntax.mk_list (es', ty) end

and strip_annot_pes tm = let
  val (pes, ty) = listSyntax.dest_list tm
  val pes' = map (fn tm => let
      val (p, e) = pairLib.dest_pair tm
      val (p', e') = (strip_annot_pat p, strip_annot_exp e)
    in pairLib.mk_pair (p', e') end) pes
in listSyntax.mk_list (pes', ty) end

and strip_annot_funs tm = let
  val (funs, ty) = listSyntax.dest_list tm
  val funs' = map (fn tm => let
      val (f,x,e) = dest_triple tm
      val e' = strip_annot_exp e
    in mk_triple (f, x, e') end) funs
in listSyntax.mk_list (funs', ty) end

(* The normalisation pass itself *)

fun dest_opapp e = let
  val (app_op, args_tm) = dest_App e
  val _ = assert (same_const Opapp) app_op
  val fx = listSyntax.dest_list args_tm |> fst
  val f = el 1 fx
  val x = el 2 fx
in
  case dest_opapp f of
     SOME (f', args) => SOME (f', args @ [x])
   | NONE => SOME (f, [x])
end
handle _ => NONE

fun mk_opapp xs =
  List.foldl (fn (x, acc) =>
    mk_App (
      Opapp,
      listSyntax.mk_list ([acc, x], exp_ty)
    )
  ) (List.hd xs) (List.tl xs)

fun fresh_name_in used = let
  fun aux n used = let
    val v = " v" ^ (Int.toString n)
  in
    if mem v used then aux (n + 1) used
    else v
  end
in
  aux 0 used
end

fun mk_names_generator () = let
  val used = ref []
  fun get () = let
    val name = fresh_name_in (!used)
  in
    used := name :: !used;
    name
  end
  fun record name =
    used := name :: !used
in (get, record) end

fun record_pat_names record_var pat =
  if pat ~~ Pany then ()
  else if is_Pvar pat then
    record_var (dest_Pvar pat)
  else if is_Plit pat then ()
  else if is_Pcon pat then let
    val (_, pats_tm) = dest_Pcon pat
    val (pats, _) = listSyntax.dest_list pats_tm
  in List.app (record_pat_names record_var) pats end
  else if is_Pref pat then
    record_pat_names record_var (dest_Pref pat)
  else if is_Ptannot pat then
   record_pat_names record_var (fst (dest_Ptannot pat))
  else raise (ERR "unknown constructor" "record_pat_names")

fun Lets [] body = body
  | Lets ((n,x) :: xs) body =
    mk_Let (optionLib.mk_some n, x, Lets xs body)

fun Let_NONE e1 e2 =
  mk_Let (
    optionLib.mk_none mlstringSyntax.mlstring_ty,
    e1,
    e2
  )

fun is_App_Opapp e =
  (is_App e) andalso fst (dest_App e) ~~ Opapp

fun norm_exp gen e = let
  val (fresh, record_name) = gen
  fun record_var v =
    record_name (mlstringSyntax.dest_mlstring v)

  fun wrap_if_needed needs_wrapping e b =
    if needs_wrapping then (
      let val x = fresh () |> mlstringSyntax.mk_mlstring in
      (mk_Var (mk_Short x), b @ [(x, e)])
      end
    ) else (e, b)

  fun norm is_named as_value e =
    if is_Lit e then
      (e, [])
    else if is_Var e then let
      val name = dest_Var e
      val _ = record_var (dest_Short name)
              handle HOL_ERR _ => ()
    in (e, []) end
    else if is_Let e then let
      val (opt, e1, e2) = dest_Let e
    in
      if optionLib.is_some opt then let
        val x = optionLib.dest_some opt
        val _ = record_var x
        val (e1', b1) = norm true false e1
        val e2' = protect false e2
        val e' = Lets b1 (Lets [(x, e1')] e2')
      in wrap_if_needed as_value e' [] end
      else let
        val (e1', b1) = norm false false e1
        val e2' = protect false e2
      in wrap_if_needed as_value (Let_NONE e1' e2') b1 end
    end
    else if is_App_Opapp e then
      case dest_opapp e of
         SOME (f, args) => let
          val (f', b0) = norm false true f
          val (args', bi) = norm_list_aux false true args
          val e' = mk_opapp (f' :: args')
          val b' = flatten (rev (b0 :: bi)) (* right-to-left evaluation *)
        in wrap_if_needed as_value e' b' end
       | NONE => fail ()
    else if is_App e then let
      val (op_, args) = dest_App e
      val (args', bi) = norm_list false true args
      val b' = flatten (rev bi) (* right-to-left evaluation *)
    in wrap_if_needed as_value (mk_App (op_, args')) b' end
    else if is_Con e then let
      val (x, args) = dest_Con e
      val (args', bi) = norm_list false true args
      val b = flatten (rev bi) (* right-to-left evaluation *)
    in wrap_if_needed as_value (mk_Con (x, args')) b end
    else if is_Raise e then let
      val exn = dest_Raise e
      val (exn', b) = norm false true exn
    in wrap_if_needed as_value (mk_Raise exn') b end
    else if is_Log e then let
      val (l, e1, e2) = dest_Log e
      val (e1', b1) = norm false true e1
      val (e2', b2) = norm false true e2
    in
      if List.null b2 then (
        if List.null b1 then (
          (* produce: <e1> op <e2> *)
          (mk_Log (l, e1', e2'), [])
        ) else (
          (* produce: let <b1> in <e1> op <e2> *)
          wrap_if_needed as_value (mk_Log (l, e1', e2')) b1
        )
      ) else (
        let val (e2', b2) = norm false false e2 in
        if l ~~ Andalso then
          (* produce: let <b1> in <e1'> andalso (lets <b2> in <e2'>) *)
          wrap_if_needed as_value (mk_Log (Andalso, e1', Lets b2 e2')) b1
        else if l ~~ Orelse then
          (* produce: let <b1> in <e1'> orelse (let <b2> in <e2'>) *)
          wrap_if_needed as_value (mk_Log (Orelse, e1', Lets b2 e2')) b1
        else fail ()
        end
      )
    end
    else if is_Fun e then let
      val (v, body) = dest_Fun e
      val _ = record_var v
      val body' = protect is_named body
    in wrap_if_needed (as_value orelse (not is_named)) (mk_Fun (v, body')) [] end
    else if is_Mat e then let
      val (e1, e2) = dest_Mat e
      val (e1', b1) = norm false true e1
      val rows' = norm_rows e2
      val e' = mk_Mat (e1', rows')
    in wrap_if_needed as_value e' b1 end
    else if is_Handle e then let
      val (e1, e2) = dest_Handle e
      val e1' = protect false e1
      val rows' = norm_rows e2
      val e' = mk_Handle (e1', rows')
    in wrap_if_needed as_value e' [] end
    else if is_If e then let
      val (e1, e2, e3) = dest_If e
      val (e1', b) = norm false true e1
      val e2' = protect false e2
      val e3' = protect false e3
    in wrap_if_needed as_value (mk_If (e1', e2', e3')) b end
    else if is_Letrec e then let
      val (rs, body) = dest_Letrec e
      val rs' = norm_letrec_branches rs
      val body' = protect false body
    in wrap_if_needed as_value (mk_Letrec (rs', body')) [] end
    else if is_Tannot e then let
      val (e, _) = dest_Tannot e
    in norm is_named as_value e end
    else if is_Lannot e then let
      val (e, _) = dest_Lannot e
    in norm is_named as_value e end
    else raise (ERR "unknown constructor" "norm")

  and norm_list is_named as_value l_tm = let
    val (l, ty) = listSyntax.dest_list l_tm
    val (es, bs) = norm_list_aux is_named as_value l
    val es_tm = listSyntax.mk_list (es, exp_ty)
  in (es_tm, bs) end

  and norm_list_aux is_named as_value [] = ([], [])
    | norm_list_aux is_named as_value (e::es) = let
      val (e', b) = norm is_named as_value e
      val (es', bs) = norm_list_aux is_named as_value es
    in (e' :: es', b :: bs) end

  and norm_rows l_tm = let
    val (l, ty) = listSyntax.dest_list l_tm
    val l' = norm_rows_aux l
  in listSyntax.mk_list (l', ty) end

  and norm_rows_aux [] = []
    | norm_rows_aux (row :: rows) = let
      val row' = protect_row false row
      val rows' = norm_rows_aux rows
    in row' :: rows' end

  and norm_letrec_branches l_tm = let
    val (l, ty) = listSyntax.dest_list l_tm
    val l' = norm_letrec_branches_aux l
  in listSyntax.mk_list (l', ty) end

  and norm_letrec_branches_aux [] = []
    | norm_letrec_branches_aux (branch :: branches) = let
      val branch' = protect_letrec_branch true branch
      val branches' = norm_letrec_branches_aux branches
    in branch' :: branches'  end

  and protect is_named e = let
    val (e', b) = norm is_named false e
  in Lets b e' end

  and protect_row is_named row = let
    val (row_pat, row_body) = pairLib.dest_pair row
    val _ = record_pat_names record_var row_pat
    val row_e' = protect is_named row_body
  in pairLib.mk_pair (row_pat, row_e') end

  and protect_letrec_branch is_named branch = let
    val (f, x, body) = dest_triple branch
    val _ = record_var f
    val _ = record_var x
    val body' = protect is_named body
  in mk_triple (f, x, body') end

in
  protect true e
end

fun strip_annot_decl d =
  if is_Dlet d then let
    val (locs, pat, exp) = dest_Dlet d
    val pat' = strip_annot_pat pat
    val exp' = strip_annot_exp exp
  in mk_Dlet (locs, pat', exp') end
  else if is_Dletrec d then let
    val (locs, funs) = dest_Dletrec d
    val funs' = strip_annot_funs funs
  in mk_Dletrec (locs, funs') end
  else d

fun strip_annot_prog p_tm = let
  val (p, p_ty) = listSyntax.dest_list p_tm
  val p' = List.map strip_annot_decl p
in listSyntax.mk_list (p', p_ty) end

fun normalise_exp e =
  norm_exp (mk_names_generator ()) (strip_annot_exp e)

fun normalise_decl d =
  if is_Dlet d then let
    val (locs, pat, exp) = dest_Dlet d
    val exp' = normalise_exp exp
  in mk_Dlet (locs, pat, exp') end
  else if is_Dletrec d then let
    val (locs, l_tm) = dest_Dletrec d
    val (l, l_ty) = listSyntax.dest_list l_tm
    val gen = mk_names_generator ()
    fun record_var v = snd gen (mlstringSyntax.dest_mlstring v)
    val l' = List.map (fn fdecl => let
      val (f, x, body) = dest_triple fdecl
      val _ = (record_var f; record_var x)
      val body' = norm_exp gen (strip_annot_exp body)
    in mk_triple (f, x, body') end) l
    val l'_tm = listSyntax.mk_list (l', l_ty)
  in mk_Dletrec (locs, l'_tm) end
  else d

fun normalise_prog p_tm = let
  val (p, p_ty) = listSyntax.dest_list p_tm
  val p' = List.map normalise_decl p
in listSyntax.mk_list (p', p_ty) end

end
