module Compiler where
import Scheme
import Prettyprinter (Pretty(pretty), (<+>), lparen, rparen, parens, line, nest, dquotes, vsep)
import System.IO (hPutStrLn, stderr)
import Control.Monad ((<=<), foldM)

compile (ConstExp (SNum x)) = Right $ parens $ pretty "SInt" <+> pretty x
compile (ConstExp (SBool False)) = Right $ parens $ pretty "SBool" <+> pretty "False"
compile (ConstExp (SBool True)) = Right $ parens $ pretty "SBool" <+> pretty "True"

compile (Apply (PrimExp Plus) xs) = foldM add (pretty "(SInt 0)") xs where
    add p x = parens . ((pretty "sadd" <+> p) <+>) <$> compile x

compile (Apply (PrimExp Multiply) xs) = foldM multiply (pretty "(SInt 1)") xs where
    multiply p x = parens . ((pretty "smul" <+> p) <+>) <$> compile x

compile (Cond c x y) = do
    cond <- compile c
    ifTrue <- compile x
    ifFalse <- compile y
    return $ parens $ pretty "if" <+> cond <+> pretty "then" <+> ifTrue <+> pretty "else" <+> ifFalse

compile (Equiv x y) = do
    left <- compile x
    right <- compile y
    return $ parens $ left <+> pretty "=" <+> right

compile (Display x) = parens . (pretty "print_sval" <+>) <$> compile x
compile (Begin (x:xs)) = parens <$> foldl state (compile x) xs where
    state p y = (<>) . (<> pretty ";") <$> p <*> compile y

inContext x = vsep [pretty "datatype sval = SInt int | SBool bool;",
    line <> nest 4 (vsep [pretty "fun print_sval v = case v of",
        pretty "SInt i => print_int i",
        pretty "| SBool b => print_pp (pp_bool b);"]),
    line <> pretty "exception SchemeArith string;",
    line <> nest 4 (vsep [pretty "fun sadd x y = case (x, y) of",
        pretty "(SInt a, SInt b) => SInt (a + b)",
        pretty "| (_, _) => raise SchemeArith" <+> dquotes (pretty "Argument to + must be a number") <> pretty ';']),
    line <> nest 4 (vsep [pretty "fun smul x y = case (x, y) of",
        pretty "(SInt a, SInt b) => SInt (a * b)",
        pretty "| (_, _) => raise SchemeArith" <+> dquotes (pretty "Argument to * must be a number") <> pretty ';']),
    line <> pretty "val _ =" <+> parens x <+> pretty "handle SchemeArith msg => TextIO.print_err msg;"
    ]

main = either (hPutStrLn stderr) (print . inContext . head)
    . (mapM compile <=< mapM toAst <=< parse [] [] <=< schlex []) =<< getContents
