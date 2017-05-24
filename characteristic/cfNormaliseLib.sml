structure cfNormaliseLib = struct

open preamble
open astSyntax

fun remove_Lannot e =
  if is_Lannot e then fst (dest_Lannot e)
  else e

fun dest_opapp e = let
  val (app_op, args_tm) = dest_App e
  val _ = assert (curry op= Opapp) app_op
  val ([f, x], _) = listSyntax.dest_list args_tm
  val f = remove_Lannot f
  val x = remove_Lannot x
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

val alpha = List.tabulate (26, fn n => Char.chr (n + Char.ord #"a") |> Char.toString)

fun fresh_name_in used = let
  fun aux n used = let
    val v = "t" ^ (Int.toString n)
  in
    if mem v used then aux (n + 1) used
    else v
  end
  val ws = subtract alpha used
in
  case ws of
     [] => aux 0 used
   | w :: _ => w
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
  if pat = Pany then ()
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
  else fail ()

fun Lets [] body = body
  | Lets ((n,x) :: xs) body =
    mk_Let (optionLib.mk_some n, x, Lets xs body)

fun Let_NONE e1 e2 =
  mk_Let (
    optionLib.mk_none stringSyntax.string_ty,
    e1,
    e2
  )

fun is_App_Opapp e =
  (is_App e) andalso fst (dest_App e) = Opapp

fun norm_exp gen e = let
  val (fresh, record_name) = gen
  fun record_var v =
    record_name (stringLib.fromHOLstring v)

  fun wrap_if_needed needs_wrapping e b =
    if needs_wrapping then (
      let val x = fresh () |> stringSyntax.fromMLstring in
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
      if b2 = [] then (
        if b1 = [] then (
          (* produce: <e1> op <e2> *)
          (mk_Log (l, e1', e2'), [])
        ) else (
          (* produce: let <b1> in <e1> op <e2> *)
          wrap_if_needed as_value (mk_Log (l, e1', e2')) b1
        )
      ) else (
        let val (e2', b2) = norm false false e2 in
        if l = And then
          (* produce: let <b1> in <e1'> andalso (lets <b2> in <e2'>) *)
          wrap_if_needed as_value (mk_Log (And, e1', Lets b2 e2')) b1
        else if l = Or then
          (* produce: let <b1> in <e1'> orelse (let <b2> in <e2'>) *)
          wrap_if_needed as_value (mk_Log (Or, e1', Lets b2 e2')) b1
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
    else fail ()

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
    val (f, p) = pairLib.dest_pair branch
    val (x, body) = pairLib.dest_pair p
    val _ = record_var f
    val _ = record_var x
    val body' = protect is_named body
  in pairLib.mk_pair (f, pairLib.mk_pair (x, body')) end

in
  protect true e
end

fun full_normalise_exp e =
  norm_exp (mk_names_generator ()) e

fun full_normalise_decl d =
  if is_Dlet d then let
    val (locs, pat, exp) = dest_Dlet d
    val exp' = full_normalise_exp exp
  in mk_Dlet (locs, pat, exp') end
  else if is_Dletrec d then let
    val (locs, l_tm) = dest_Dletrec d
    val (l, l_ty) = listSyntax.dest_list l_tm
    val gen = mk_names_generator ()
    fun record_var v = snd gen (stringLib.fromHOLstring v)
    val l' = List.map (fn fdecl => let
      val (f, p) = pairLib.dest_pair fdecl
      val (x, body) = pairLib.dest_pair p
      val _ = (record_var f; record_var x)
      val body' = norm_exp gen body
    in pairLib.mk_pair (f, pairLib.mk_pair (x, body')) end) l
    val l'_tm = listSyntax.mk_list (l', l_ty)
  in mk_Dletrec (locs, l'_tm) end
  else d

fun full_normalise_top td =
  if is_Tdec td then let
    val d = dest_Tdec td
    val d' = full_normalise_decl d
  in mk_Tdec d' end
  else td

fun full_normalise_prog p_tm = let
  val (p, p_ty) = listSyntax.dest_list p_tm
  val p' = List.map full_normalise_top p
in listSyntax.mk_list (p', p_ty) end

end
