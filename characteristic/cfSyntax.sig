signature cfSyntax = sig
  include Abbrev

  (* cf_let let var expr env H Q *)
  val cf_let_tm   : term
  val mk_cf_let   : term * term * term * term * term * term -> term
  val dest_cf_let : term -> term * term * term * term * term * term
  val is_cf_let   : term -> bool

  (* cf_lit lit env H Q *)
  val cf_lit_tm   : term
  val mk_cf_lit   : term * term * term * term -> term
  val dest_cf_lit : term -> term * term * term * term
  val is_cf_lit   : term -> bool

  (* cf_con cname args env H Q *)
  val cf_con_tm   : term
  val mk_cf_con   : term * term * term * term * term -> term
  val dest_cf_con : term -> term * term * term * term * term
  val is_cf_con   : term -> bool

  (* cf_var name env H Q *)
  val cf_var_tm   : term
  val mk_cf_var   : term * term * term * term -> term
  val dest_cf_var : term -> term * term * term * term
  val is_cf_var   : term -> bool

  (* cf_fun p f ns F1 F2 env H Q *)
  val cf_fun_tm   : term
  val mk_cf_fun   : term * term * term * term * term * term * term * term ->
                    term
  val dest_cf_fun : term ->
                    term * term * term * term * term * term * term * term
  val is_cf_fun   : term -> bool

  (* cf_fun_rec p fs_FS F2 env H Q *)
  val cf_fun_rec_tm   : term
  val mk_cf_fun_rec   : term * term * term * term * term * term -> term
  val dest_cf_fun_rec : term -> term * term * term * term * term * term
  val is_cf_fun_rec   : term -> bool

  (* cf_app p f args env H Q *)
  val cf_app_tm   : term
  val mk_cf_app   : term * term * term * term * term * term -> term
  val dest_cf_app : term -> term * term * term * term * term * term
  val is_cf_app   : term -> bool

  (* cf_log lop e1 e2 env H Q *)
  val cf_log_tm : term
  val mk_cf_log   : term * term * term * term * term * term -> term
  val dest_cf_log : term -> term * term * term * term * term * term
  val is_cf_log   : term -> bool

  (* cf_if cond e1 e2 env H Q *)
  val cf_if_tm : term
  val mk_cf_if   : term * term * term * term * term * term -> term
  val dest_cf_if : term -> term * term * term * term * term * term
  val is_cf_if   : term -> bool

  (* cf_match e branches env H Q *)
  val cf_match_tm : term
  val mk_cf_match   : term * term * term * term * term -> term
  val dest_cf_match : term -> term * term * term * term * term
  val is_cf_match   : term -> bool

  (* cf_handle e branches env H Q *)
  val cf_handle_tm : term
  val mk_cf_handle   : term * term * term * term * term -> term
  val dest_cf_handle : term -> term * term * term * term * term
  val is_cf_handle   : term -> bool

  (* cf_raise e env H Q *)
  val cf_raise_tm   : term
  val mk_cf_raise   : term * term * term * term -> term
  val dest_cf_raise : term -> term * term * term * term
  val is_cf_raise   : term -> bool

end
