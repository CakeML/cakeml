module InitialProgram where
import Ast
import Text.Parsec.Pos (SourcePos)

vn x = VarN x dummy_pos
cn x = ConN x dummy_pos
tn x = TypeN x dummy_pos
tv x = TvarN x dummy_pos
mn x = ModN x dummy_pos


x = VarN "x" dummy_pos
y = VarN "y" dummy_pos

mk_binop :: String -> (SourcePos -> Op) -> Dec
mk_binop name prim =
  Dlet (Pvar (vn name)) (Fun x (Fun y (App (prim dummy_pos) [Var (Short x), Var (Short y)]) dummy_pos) dummy_pos) dummy_pos

mk_unop :: String -> (SourcePos -> Op) -> Dec
mk_unop name prim =
  Dlet (Pvar (vn name)) (Fun x (App (prim dummy_pos) [Var (Short x)]) dummy_pos) dummy_pos

prim_types_program :: Prog
prim_types_program =
  [Tdec (Dexn (cn "Bind") []),
   Tdec (Dexn (cn "Chr") []),
   Tdec (Dexn (cn "Div") []),
   Tdec (Dexn (cn "Eq") []),
   Tdec (Dexn (cn "Subscript") []),
   Tdec (Dtype [([], tn "bool", [(cn "true", []), (cn "false", [])])]),
   Tdec (Dtype [([tv "'a"], tn "list", [(cn "nil", []), (cn "::", [Tvar (tv "'a"), Tapp [Tvar (tv "'a")] (TC_name (Short (tn "list")))])])]),
   Tdec (Dtype [([tv "'a"], tn "option", [(cn "NONE", []),(cn "SOME", [Tvar (tv "'a")])])])]


basis_program :: Prog
basis_program =
  [Tdec (Dtabbrev [] (tn "int") (Tapp [] TC_int)),
   Tdec (Dtabbrev [] (tn "string") (Tapp [] TC_string)),
   Tdec (Dtabbrev [] (tn "unit") (Tapp [] TC_tup)),
   Tdec (Dtabbrev [tv "'a"] (tn "ref") (Tapp [Tvar (tv "'a")] TC_ref)),
   Tdec (Dtabbrev [] (tn "exn") (Tapp [] TC_exn)),
   Tdec (mk_binop "+" (Opn Plus)),
   Tdec (mk_binop "-" (Opn Minus)),
   Tdec (mk_binop "*" (Opn Times)),
   Tdec (mk_binop "div" (Opn Divide)),
   Tdec (mk_binop "mod" (Opn Modulo)),
   Tdec (mk_binop "<" (Opb Lt)),
   Tdec (mk_binop ">" (Opb Gt)),
   Tdec (mk_binop "<=" (Opb Leq)),
   Tdec (mk_binop ">=" (Opb Geq)),
   Tdec (mk_binop "=" Equality),
   Tdec (mk_binop ":=" Opassign),
   Tdec (Dlet (Pvar (vn "~")) (Fun x (App (Opn Minus dummy_pos) [Lit (IntLit 0) dummy_pos, Var (Short (vn "x"))]) dummy_pos) dummy_pos),
   Tdec (mk_unop "!" Opderef),
   Tdec (mk_unop "ref" Opref),
   Tmod (mn "Word8") Nothing 
     [Dtabbrev [] (tn "word") (Tapp [] TC_word8)],
   Tmod (mn "Word8Array") Nothing 
     [Dtabbrev [] (tn "array") (Tapp [] TC_word8array),
      Dtabbrev [] (tn "elem") (Tapp [] TC_word8),
      mk_binop "array" Aw8alloc,
      mk_binop "sub" Aw8sub,
      mk_unop "length" Aw8length,
      Dlet (Pvar (vn "update")) (Fun x (Fun y (Fun (vn "z") (App (Aw8update dummy_pos) [Var (Short x), Var (Short y), Var (Short (vn "z"))]) dummy_pos) dummy_pos) dummy_pos) dummy_pos ],
   Tmod (mn "Vector") Nothing
     [Dtabbrev [tv "'a"] (tn "vector") (Tapp [Tvar (tv "'a")] TC_vector),
      mk_unop "fromList" VfromList,
      mk_unop "length" Vlength,
      mk_binop "sub" Vsub],
   Tmod (mn "Array") Nothing 
     [Dtabbrev [tv "'a"] (tn "array") (Tapp [Tvar (tv "'a")] TC_array),
      mk_binop "array" Aalloc,
      mk_binop "sub" Asub,
      mk_unop "length" Alength,
      Dlet (Pvar (vn "update")) (Fun x (Fun y (Fun (vn "z") (App (Aupdate dummy_pos) [Var (Short x), Var (Short y), Var (Short (vn "z"))]) dummy_pos) dummy_pos) dummy_pos)  dummy_pos],
   Tmod (mn "Char") Nothing
     [Dtabbrev [] (tn "char") (Tapp [] TC_char),
      mk_unop "ord" Ord,
      mk_unop "chr" Chr,
      mk_binop "<" (Chopb Lt),
      mk_binop "<=" (Chopb Leq),
      mk_binop ">" (Chopb Gt),
      mk_binop ">=" (Chopb Geq)],
   Tmod (mn "String") Nothing
     [Dtabbrev [] (tn "string") (Tapp [] TC_string),
      mk_unop "explode" Explode,
      mk_unop "implode" Implode,
      mk_unop "size" Strlen]]
