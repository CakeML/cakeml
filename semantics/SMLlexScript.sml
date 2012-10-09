open preamble;
open lcsymtacs;
open intLib;
open lexer_specTheory;
open TokensTheory

val _ = new_theory "SMLlex";

val string_to_num_def = Define `
(string_to_num "" = 0) ∧
(string_to_num (c::s) =
   (ORD c - (48:num)) + 10 * string_to_num s)`;

val string_to_int_def = Define `
(string_to_int (#"~"::s) = (0:int) - &(string_to_num (REVERSE s))) ∧
(string_to_int s = &(string_to_num (REVERSE s)))`;

(*
The standard ML lexer is translated directly from Hamlet, which has this
license:

Copyright (c) 1999-2007 Andreas Rossberg

All rights reserved.

The following terms apply to all files associated with this software and its
documentation, with the exception of individual files that explicitly state
their own licensing terms.

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the "Software"),
to deal in the Software without restriction, including without limitation
the rights to use, copy, modify, merge, publish, distribute, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, provided that the above copyright notice(s) and this
permission notice appear in all copies of the Software and that both the
above copyright notice(s) and this permission notice appear in supporting
documentation.

The Software is provided "as is", without warranty of any kind, express or
implied, including but not limited to the warranties of merchantability,
fitness for a particular purpose and noninfringement of third party rights.
In no event shall the copyright holder or holders included in this notice
be liable for any claim, or any special indirect or consequential damages,
or any damages whatsoever resulting from loss of use, data or profits,
whether in an action of contract, negligence or other tortious action,
arising out of or in connection with the use or performance of this
software.

Except as contained in this notice, the name of a copyright holder shall
not be used in advertising or otherwise to promote the sale, use or other
dealings in this Software without prior written authorization of the
copyright holder.

*)


val formatting_def = Define `
formatting = Plus (CharSet (set " \t\n\011\012\013"))`;

val letter_def = Define `
letter = CharSet (set "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz")`;

val symbol_def = Define `
symbol = CharSet (set "-!%&$#+/:<=>?@\\~\096|*\094")`;

val digit_def = Define `
digit = CharSet (set "0123456789")`;

val digit_not_zero_def = Define `
digit_not_zero = CharSet (set "123456789")`;

val hexdigit_def = Define `
hexdigit = CharSet (set "0123456789ABCDEFabcdef")`;

val posdecint_def = Define `
posdecint = Plus digit`;

val poshexint_def = Define `
poshexint = Cat (StringLit "0x") (Plus hexdigit)`;

val negdecint_def = Define `
negdecint = Cat (StringLit "~") posdecint`;

val neghexint_def = Define `
neghexint = Cat (StringLit "~") poshexint`;

val decint_def = Define `
decint = Or [posdecint; negdecint]`;

val hexint_def = Define `
hexint = Or [poshexint; neghexint]`;

val decword_def = Define `
decword = Cat (StringLit "0w") (Plus digit)`;

val hexword_def = Define `
hexword = Cat (StringLit "0wx") (Plus hexdigit)`;

val exp_def = Define `
exp = CharSet (set "Ee")`;

val real_def = Define `
real = Or [ Cat decint
           (Cat (StringLit ".")
           (Cat (Plus digit)
                (Or [Cat exp decint; StringLit ""])));
           (Cat decint (Cat exp decint))]`;

val numericlab_def = Define `
numericlab = Cat digit_not_zero (Plus digit)`;

val alphanumid_def = Define `
alphanumid = Cat letter (Star (Or [letter; digit; CharSet (set "_'")]))`;

val symbolicid_def = Define `
symbolicid = Plus symbol`;

val id_def = Define `
id = Or [alphanumid; symbolicid]`;

val tyvar_def = Define `
tyvar = Cat (StringLit "'") (Star (Or [letter; digit; CharSet (set "_'")]))`;

val longid_def = Define `
longid = Cat (Plus (Cat alphanumid (StringLit ".")))
             (Or [id; StringLit "="; StringLit "*"])`;

val printable = Define `
printable = CharSet (set
"!#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[]\094_\096abcdefghijklmnopqrstuvwxyz{|}~")`;

val escape_def = Define `
escape = Or [StringLit "\\a"; StringLit "\\b"; StringLit "\\t"; StringLit "\\n";
             StringLit "\\v"; StringLit "\\f"; StringLit "\\r";
	     Cat (StringLit "\\\094") (CharSet (set "@-_"));
             Cat (StringLit "\\") (Cat digit (Cat digit digit));
             Cat (StringLit "\\u")
                 (Cat hexdigit (Cat hexdigit (Cat hexdigit hexdigit)));
	     StringLit "\\\"";
             StringLit "\\\\"]`;

val gap_def = Define `
gap = Cat (StringLit "\\") (Cat formatting (StringLit "\\"))`;

val stringchar_def = Define `
stringchar = Or [printable; StringLit " "; escape]`;

val string_def = Define `
string = Cat (StringLit "\"")
             (Cat (Star (Or [stringchar; gap])) (StringLit "\""))`;

val char_def = Define `
char = Cat (StringLit "#\"")
           (Cat (Star gap) (Cat stringchar (Cat (Star gap) (StringLit "\""))))`;

val SML_lex_spec_def = Define `
SML_lex_spec : token lexer_spec =
[(StringLit "\n",        (\s. NewlineT));
 (Plus (CharSet (set " \t\011\012\013")),
                         (\s. WhitespaceT (STRLEN s)));
 (StringLit "#",         (\s. HashT));
 (StringLit "(",         (\s. LparT));
 (StringLit ")",         (\s. RparT));
 (StringLit "*",         (\s. StarT));
 (StringLit ",",         (\s. CommaT));
 (StringLit "->",        (\s. ArrowT));
 (StringLit "...",       (\s. DotsT));
 (StringLit ":",         (\s. ColonT));
 (StringLit ":>",        (\s. SealT));
 (StringLit ";",         (\s. SemicolonT));
 (StringLit "=",         (\s. EqualsT));
 (StringLit "=>",        (\s. DarrowT));
 (StringLit "[",         (\s. LbrackT));
 (StringLit "]",         (\s. RbrackT));
 (StringLit "_",         (\s. UnderbarT));
 (StringLit "{",         (\s. LbraceT));
 (StringLit "|",         (\s. BarT));
 (StringLit "}",         (\s. RbraceT));
 (StringLit "abstype",   (\s. AbstypeT));
 (StringLit "and",       (\s. AndT));
 (StringLit "andalso",   (\s. AndalsoT));
 (StringLit "as",        (\s. AsT));
 (StringLit "case",      (\s. CaseT));
 (StringLit "datatype",  (\s. DatatypeT));
 (StringLit "do",        (\s. DoT));
 (StringLit "else",      (\s. ElseT));
 (StringLit "end",       (\s. EndT));
 (StringLit "eqtype",    (\s. EqtypeT));
 (StringLit "exception", (\s. ExceptionT));
 (StringLit "fn",        (\s. FnT));
 (StringLit "fun",       (\s. FunT));
 (StringLit "functor",   (\s. FunctorT));
 (StringLit "handle",    (\s. HandleT));
 (StringLit "if",        (\s. IfT));
 (StringLit "in",        (\s. InT));
 (StringLit "include",   (\s. IncludeT));
 (StringLit "infix",     (\s. InfixT));
 (StringLit "infixr",    (\s. InfixrT));
 (StringLit "let",       (\s. LetT));
 (StringLit "local",     (\s. LocalT));
 (StringLit "nonfix",    (\s. NonfixT));
 (StringLit "of",        (\s. OfT));
 (StringLit "op",        (\s. OpT));
 (StringLit "open",      (\s. OpenT));
 (StringLit "orelse",    (\s. OrelseT));
 (StringLit "raise",     (\s. RaiseT));
 (StringLit "rec",       (\s. RecT));
 (StringLit "sharing",   (\s. SharingT));
 (StringLit "sig",       (\s. SigT));
 (StringLit "signature", (\s. SignatureT));
 (StringLit "struct",    (\s. StructT));
 (StringLit "structure", (\s. StructureT));
 (StringLit "then",      (\s. ThenT));
 (StringLit "type",      (\s. TypeT));
 (StringLit "val",       (\s. ValT));
 (StringLit "where",     (\s. WhereT));
 (StringLit "while",     (\s. WhileT));
 (StringLit "with",      (\s. WithT));
 (StringLit "withtype",  (\s. WithtypeT));
 (StringLit "0",         (\s. ZeroT));
 (digit_not_zero,        (\s. DigitT s));
 (numericlab,            (\s. NumericT s));
 (decint,                (\s. IntT (string_to_int s)));
 (hexint,                (\s. HexintT s));
 (decword,               (\s. WordT s));
 (hexword,               (\s. HexwordT s));
 (real,                  (\s. RealT s));
 (string,                (\s. StringT s));
 (char,                  (\s. CharT s));
 (tyvar,                 (\s. TyvarT (TL s)));
 (alphanumid,            (\s. AlphaT s));
 (symbolicid,            (\s. SymbolT s));
 (longid,                (\s. LongidT s))]`;


val _ = export_theory ();

