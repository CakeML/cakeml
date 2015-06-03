module Ast where
import Data.Map as Map
import Data.List as List
import Data.Maybe as Maybe
import Data.Word as Word
import Text.Parsec.Pos (SourcePos, initialPos)

dummy_pos = initialPos "compiler generated"

class HasPos a where
  getPos :: a -> SourcePos

data Lit = 
    IntLit Integer
  | Char Char
  | StrLit String
  | Word8 Word8
  deriving Eq

instance Show Lit where
  show (IntLit i) = 
    if i >= 0 then
      show i
    else
      '~' : show (-i)
  show (Char c) = "#\"" ++ show c ++ "\""  -- TODO Cake-ify
  show (StrLit s) = "\"" ++ show s ++ "\"" -- TODO Cakeify
  show (Word8 w) = show w  -- TODO Cakeify

data Opn = Plus | Minus | Times | Divide | Modulo
  deriving Eq

data Opb = Lt | Gt | Leq | Geq

data ModN = ModN String SourcePos

instance HasPos ModN where
  getPos (ModN _ p) = p

instance Eq ModN where
  (==) (ModN x _) (ModN y _) = x == y

instance Ord ModN where
  compare (ModN x _) (ModN y _) = compare x y

instance Show ModN where
  show (ModN x _) = x

data Id a = Short a
          | Long ModN a
  deriving (Eq, Ord)

instance HasPos a => HasPos (Id a) where
  getPos (Long m a) = getPos a
  getPos (Short a) = getPos a

instance Show a => Show (Id a) where
  show (Short x) = show x
  show (Long x y) = show x ++ "." ++ show y

data VarN = VarN String SourcePos

instance HasPos VarN where
  getPos (VarN _ p) = p

instance Eq VarN where
  (==) (VarN x _) (VarN y _) = x == y

instance Ord VarN where
  compare (VarN x _) (VarN y _) = compare x y

instance Show VarN where
  show (VarN x _) = x

data ConN = ConN String SourcePos

instance HasPos ConN where
  getPos (ConN _ p) = p

instance Eq ConN where
  (==) (ConN x _) (ConN y _) = x == y

instance Ord ConN where
  compare (ConN x _) (ConN y _) = compare x y

instance Show ConN where
  show (ConN x _) = x

data TypeN = TypeN String SourcePos

instance Eq TypeN where
  (==) (TypeN x _) (TypeN y _) = x == y

instance Ord TypeN where
  compare (TypeN x _) (TypeN y _) = compare x y

instance Show TypeN where
  show (TypeN x _) = x

instance HasPos TypeN where
  getPos (TypeN _ p) = p

data TvarN = TvarN String SourcePos

instance HasPos TvarN where
  getPos (TvarN _ p) = p

instance Eq TvarN where
  (==) (TvarN x _) (TvarN y _) = x == y

instance Ord TvarN where
  compare (TvarN x _) (TvarN y _) = compare x y

instance Show TvarN where
  show (TvarN x _) = x

mk_id :: Maybe ModN -> a -> Id a
mk_id Nothing n = Short n
mk_id (Just mn) n = Long mn n

id_to_n :: Id a -> a
id_to_n (Short n) = n
id_to_n (Long _ n) = n

data Op = 
  -- Operations on integers
    Opn Opn SourcePos
  | Opb Opb SourcePos
  -- Polymorphic =
  | Equality SourcePos
  -- Application
  | Opapp
  -- Reference operations
  | Opassign SourcePos
  | Opref SourcePos
  | Opderef SourcePos
  -- Word8Array operations
  | Aw8alloc SourcePos
  | Aw8sub SourcePos
  | Aw8length SourcePos
  | Aw8update SourcePos
  -- Char operations
  | Ord SourcePos
  | Chr SourcePos
  | Chopb Opb SourcePos
  -- String operations
  | Explode SourcePos
  | Implode SourcePos
  | Strlen SourcePos
  -- Vector operations
  | VfromList SourcePos
  | Vsub SourcePos
  | Vlength SourcePos
  -- Array operations
  | Aalloc SourcePos
  | Asub SourcePos
  | Alength SourcePos
  | Aupdate SourcePos
  -- Call a given foreign function
  | FFI Integer SourcePos

data Lop = And SourcePos | Or SourcePos

instance HasPos Lop where
  getPos (And p) = p
  getPos (Or p) = p

data Tc = 
    TC_name (Id TypeN)
  | TC_int
  | TC_char
  | TC_string
  | TC_ref
  | TC_word8
  | TC_word8array
  | TC_fn
  | TC_tup
  | TC_exn
  | TC_vector
  | TC_array
  deriving Eq

instance Show Tc where
  show (TC_name n) = show n
  show TC_int = "int"
  show TC_char = "char"
  show TC_string = "string"
  show TC_ref = "ref"
  show TC_word8 = "Word8.t"
  show TC_word8array = "Word8Array.t"
  show TC_fn = "->"
  show TC_tup = "*"
  show TC_exn = "exn"
  show TC_vector = "Vector.t"
  show TC_array = "Array.t"

data T = 
    Tvar TvarN
  | Tvar_db Integer
  | Tapp [T] Tc
  deriving Eq

instance Show T where
  show (Tvar tv) = show tv
  show (Tvar_db n) = show n
  show (Tapp ts tc) = show ts ++ show tc

tint = Tapp [] TC_int
tchar = Tapp [] TC_char
tstring = Tapp [] TC_string
tref t = Tapp [t] TC_ref
tword8 = Tapp [] TC_word8
tword8array = Tapp [] TC_word8array
tfn t1 t2 = Tapp [t1,t2] TC_fn
texn = Tapp [] TC_exn

data Pat = 
    Pvar VarN
  | Plit Lit SourcePos
  | Pcon (Maybe (Id ConN)) [Pat] SourcePos
  | Pref Pat SourcePos

data Exp = 
    Raise Exp
  | Handle Exp [(Pat,Exp)]
  | Lit Lit SourcePos
  | Con (Maybe (Id ConN)) [Exp] SourcePos
  | Var (Id VarN)
  | Fun VarN Exp SourcePos
  | App Op [Exp]
  | Log Lop Exp Exp
  | If Exp Exp Exp
  | Mat Exp [(Pat,Exp)]
  | Let (Maybe VarN) Exp Exp
  | Letrec [(VarN,VarN,Exp)] Exp

type Type_def = [([TvarN], TypeN, [(ConN, [T])])]

data Dec = 
    Dlet Pat Exp SourcePos
  | Dletrec [(VarN, VarN, Exp)]
  | Dtype Type_def
  | Dtabbrev [TvarN] TypeN T
  | Dexn ConN [T]

type Decs = [Dec]

data Spec = 
    Sval VarN T
  | Stype Type_def
  | Stabbrev [TvarN] TypeN T
  | Stype_opq [TvarN] TypeN
  | Sexn ConN [T]

type Specs = [Spec]

data Top = 
    Tmod ModN (Maybe Specs) Decs
  | Tdec Dec

type Prog = [Top]

pat_bindings :: Pat -> [VarN] -> [VarN]
pat_bindings (Pvar n) already_bound = n:already_bound
pat_bindings (Plit l _) already_bound = already_bound
pat_bindings (Pcon _ ps _) already_bound = pats_bindings ps already_bound
pat_bindings (Pref p _) already_bound = pat_bindings p already_bound
pats_bindings [] already_bound = already_bound
pats_bindings (p:ps) already_bound = pats_bindings ps (pat_bindings p already_bound)


{- Old stuff 

newtype Env k v = Env (Map k v)

emp :: Env k v
emp = Env Map.empty

merge :: Ord k => Env k v -> Env k v -> Env k v
merge (Env m1) (Env m2) = Env (Map.union m1 m2)

bind :: Ord k => k -> v -> Env k v -> Env k v
bind k v (Env m) = Env (Map.insert k v m)

listToEnv :: Ord k => [(k,v)] -> Env k v
listToEnv l = Env (Map.fromList l)

envToList :: Env k v -> [(k,v)]
envToList (Env m) = Map.assocs m

envAll :: (k -> v -> Bool) -> Env k v -> Bool
envAll f (Env m) = List.all (\(x,y) -> f x y) (Map.assocs m)

envElem :: Ord k => k -> Env k v -> Bool
envElem k (Env m) = Map.member k m

show_pair (x,y) = "val " ++ show x ++ " = " ++ show y ++ ";"

instance (Show k, Show v) => Show (Env k v) where
  show (Env e) = List.intercalate "\n" (List.map show_pair (Map.assocs e))

opn_lookup :: Opn -> Integer -> Integer -> Integer
opn_lookup Plus = (+)
opn_lookup Minus = (-)
opn_lookup Times = ( * )
opn_lookup Divide = (div)
opn_lookup Modulo = (mod)

opb_lookup :: Opb -> Integer -> Integer -> Bool
opb_lookup Lt = (<)
opb_lookup Gt = (>)
opb_lookup Leq = (<=)
opb_lookup Geq = (>=)


data Tid_or_exn = 
    TypeId (Id TypeN)
  | TypeExn

instance Eq Tid_or_exn where
  (==) TypeExn TypeExn = True
  (==) (TypeId tid1) (TypeId tid2) = tid1 == tid2
  (==) _ _ = False



-}
