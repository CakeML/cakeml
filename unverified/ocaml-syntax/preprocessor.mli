open TypedtreeMap

module type StampRef = sig val v : int Batteries.ref end
module GuardMap :
  sig
    val map_structure : Typedtree.structure -> Typedtree.structure
    val map_pattern : Typedtree.pattern -> Typedtree.pattern
    val map_structure_item :
      Typedtree.structure_item -> Typedtree.structure_item
    val map_expression : Typedtree.expression -> Typedtree.expression
    val map_class_expr : Typedtree.class_expr -> Typedtree.class_expr
    val map_signature : Typedtree.signature -> Typedtree.signature
    val map_signature_item :
      Typedtree.signature_item -> Typedtree.signature_item
    val map_module_type : Typedtree.module_type -> Typedtree.module_type
  end
module RecordMap :
  sig
    val map_structure : Typedtree.structure -> Typedtree.structure
    val map_pattern : Typedtree.pattern -> Typedtree.pattern
    val map_structure_item :
      Typedtree.structure_item -> Typedtree.structure_item
    val map_expression : Typedtree.expression -> Typedtree.expression
    val map_class_expr : Typedtree.class_expr -> Typedtree.class_expr
    val map_signature : Typedtree.signature -> Typedtree.signature
    val map_signature_item :
      Typedtree.signature_item -> Typedtree.signature_item
    val map_module_type : Typedtree.module_type -> Typedtree.module_type
  end
module ValrecMap :
  functor (S : StampRef) ->
    sig
      val map_structure : Typedtree.structure -> Typedtree.structure
      val map_pattern : Typedtree.pattern -> Typedtree.pattern
      val map_structure_item :
        Typedtree.structure_item -> Typedtree.structure_item
      val map_expression : Typedtree.expression -> Typedtree.expression
      val map_class_expr : Typedtree.class_expr -> Typedtree.class_expr
      val map_signature : Typedtree.signature -> Typedtree.signature
      val map_signature_item :
        Typedtree.signature_item -> Typedtree.signature_item
      val map_module_type : Typedtree.module_type -> Typedtree.module_type
    end
module ValpatMap :
  sig
    val map_structure : Typedtree.structure -> Typedtree.structure
    val map_pattern : Typedtree.pattern -> Typedtree.pattern
    val map_structure_item :
      Typedtree.structure_item -> Typedtree.structure_item
    val map_expression : Typedtree.expression -> Typedtree.expression
    val map_class_expr : Typedtree.class_expr -> Typedtree.class_expr
    val map_signature : Typedtree.signature -> Typedtree.signature
    val map_signature_item :
      Typedtree.signature_item -> Typedtree.signature_item
    val map_module_type : Typedtree.module_type -> Typedtree.module_type
  end
module AnypatMap :
  functor (S : StampRef) ->
    sig
      val map_structure : Typedtree.structure -> Typedtree.structure
      val map_pattern : Typedtree.pattern -> Typedtree.pattern
      val map_structure_item :
        Typedtree.structure_item -> Typedtree.structure_item
      val map_expression : Typedtree.expression -> Typedtree.expression
      val map_class_expr : Typedtree.class_expr -> Typedtree.class_expr
      val map_signature : Typedtree.signature -> Typedtree.signature
      val map_signature_item :
        Typedtree.signature_item -> Typedtree.signature_item
      val map_module_type : Typedtree.module_type -> Typedtree.module_type
    end
module RemoveAliaspatMap :
  sig
    val map_structure : Typedtree.structure -> Typedtree.structure
    val map_pattern : Typedtree.pattern -> Typedtree.pattern
    val map_structure_item :
      Typedtree.structure_item -> Typedtree.structure_item
    val map_expression : Typedtree.expression -> Typedtree.expression
    val map_class_expr : Typedtree.class_expr -> Typedtree.class_expr
    val map_signature : Typedtree.signature -> Typedtree.signature
    val map_signature_item :
      Typedtree.signature_item -> Typedtree.signature_item
    val map_module_type : Typedtree.module_type -> Typedtree.module_type
  end
module AliaspatMap :
  sig
    val map_structure : Typedtree.structure -> Typedtree.structure
    val map_pattern : Typedtree.pattern -> Typedtree.pattern
    val map_structure_item :
      Typedtree.structure_item -> Typedtree.structure_item
    val map_expression : Typedtree.expression -> Typedtree.expression
    val map_class_expr : Typedtree.class_expr -> Typedtree.class_expr
    val map_signature : Typedtree.signature -> Typedtree.signature
    val map_signature_item :
      Typedtree.signature_item -> Typedtree.signature_item
    val map_module_type : Typedtree.module_type -> Typedtree.module_type
  end
module FunctionMap :
  functor (S : StampRef) ->
    sig
      val map_structure : Typedtree.structure -> Typedtree.structure
      val map_pattern : Typedtree.pattern -> Typedtree.pattern
      val map_structure_item :
        Typedtree.structure_item -> Typedtree.structure_item
      val map_expression : Typedtree.expression -> Typedtree.expression
      val map_class_expr : Typedtree.class_expr -> Typedtree.class_expr
      val map_signature : Typedtree.signature -> Typedtree.signature
      val map_signature_item :
        Typedtree.signature_item -> Typedtree.signature_item
      val map_module_type : Typedtree.module_type -> Typedtree.module_type
    end
module OrpatMap :
  sig
    val map_structure : Typedtree.structure -> Typedtree.structure
    val map_pattern : Typedtree.pattern -> Typedtree.pattern
    val map_structure_item :
      Typedtree.structure_item -> Typedtree.structure_item
    val map_expression : Typedtree.expression -> Typedtree.expression
    val map_class_expr : Typedtree.class_expr -> Typedtree.class_expr
    val map_signature : Typedtree.signature -> Typedtree.signature
    val map_signature_item :
      Typedtree.signature_item -> Typedtree.signature_item
    val map_module_type : Typedtree.module_type -> Typedtree.module_type
  end
module type EnvProvider = sig val env : Env.t end
module PreprocessorMapArgument :
  functor (FinalEnv : EnvProvider) -> MapArgument
module PreprocessorMap :
  functor (FinalEnv : EnvProvider) ->
    sig
      val map_structure : Typedtree.structure -> Typedtree.structure
      val map_pattern : Typedtree.pattern -> Typedtree.pattern
      val map_structure_item :
        Typedtree.structure_item -> Typedtree.structure_item
      val map_expression : Typedtree.expression -> Typedtree.expression
      val map_class_expr : Typedtree.class_expr -> Typedtree.class_expr
      val map_signature : Typedtree.signature -> Typedtree.signature
      val map_signature_item :
        Typedtree.signature_item -> Typedtree.signature_item
      val map_module_type : Typedtree.module_type -> Typedtree.module_type
    end
