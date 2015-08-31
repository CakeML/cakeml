type 'b list_context = 'b list * 'b list
type ('a, 'b) list_zipper = 'a * 'b list_context
type var_info = Ident.t * string Asttypes.loc
type pattern_context = {
  patctxt_desc : pattern_desc_context;
  patctxt_loc : Location.t;
  patctxt_extra :
    (Typedtree.pat_extra * Location.t * Typedtree.attribute list) list;
  patctxt_type : Types.type_expr;
  mutable patctxt_env : Env.t;
  patctxt_attributes : Typedtree.attribute list;
}
and pattern_desc_context =
    Tpatctxt_var
  | Tpatctxt_alias of Typedtree.pattern
  | Tpatctxt_alias_inner of pattern_context * Ident.t * string Asttypes.loc
  | Tpatctxt_tuple of (pattern_context, Typedtree.pattern) list_zipper
  | Tpatctxt_construct of Longident.t Asttypes.loc *
      Types.constructor_description *
      (pattern_context, Typedtree.pattern) list_zipper
  | Tpatctxt_variant of Asttypes.label * pattern_context *
      Types.row_desc Batteries.ref
  | Tpatctxt_record of
      (Longident.t Asttypes.loc * Types.label_description * pattern_context,
       Longident.t Asttypes.loc * Types.label_description * Typedtree.pattern)
      list_zipper * Asttypes.closed_flag
  | Tpatctxt_array of (pattern_context, Typedtree.pattern) list_zipper
  | Tpatctxt_or of pattern_context * pattern_context * Types.row_desc option
  | Tpatctxt_lazy of pattern_context
type pattern_zipper = var_info * pattern_context
type pattern_desc_zipper = var_info * pattern_desc_context
type binding =
    Longident.t Asttypes.loc * Types.label_description * Typedtree.pattern
type binding_context =
    Longident.t Asttypes.loc * Types.label_description * pattern_context
type binding_zipper = var_info * binding_context
val zipper_find : ('a -> bool) -> 'a list -> ('a, 'a) list_zipper option
val patch : 'a list_context -> 'a list
val pattern_zippers :
  (Typedtree.pattern_desc -> (var_info * pattern_desc_context) list) ->
  Typedtree.pattern -> pattern_zipper list
val pattern_list_zippers :
  (Typedtree.pattern_desc -> (var_info * pattern_desc_context) list) ->
  Typedtree.pattern list ->
  (pattern_zipper, Typedtree.pattern) list_zipper list
val binding_list_zippers :
  (Typedtree.pattern_desc -> (var_info * pattern_desc_context) list) ->
  binding list -> (binding_zipper, binding) list_zipper list
val varpat_desc_zippers : Typedtree.pattern_desc -> pattern_desc_zipper list
val varpat_zippers : Typedtree.pattern -> pattern_zipper list
val aliaspat_desc_zippers :
  Typedtree.pattern_desc -> pattern_desc_zipper list
val aliaspat_zippers : Typedtree.pattern -> pattern_zipper list
val pattern_of_zipper :
  (Ident.t * string Asttypes.loc) * pattern_context -> Typedtree.pattern
val pattern_list_of_zipper :
  Ident.t * string Asttypes.loc ->
  (pattern_context, Typedtree.pattern) list_zipper -> Typedtree.pattern list
val binding_list_of_zipper :
  Ident.t * string Asttypes.loc ->
  (Longident.t Asttypes.loc * Types.label_description * pattern_context,
   Longident.t Asttypes.loc * Types.label_description * Typedtree.pattern)
  list_zipper ->
  (Longident.t Asttypes.loc * Types.label_description * Typedtree.pattern)
  list
val inner_pattern_context : pattern_context -> pattern_context
