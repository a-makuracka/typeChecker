module Utils where

import LexLatte
import ParLatte
import AbsLatte
import ErrM



type WasThereAReturn = Bool
type IsFun = Bool

data FunType = FunType
  { funName :: Ident,
    funReturnType :: Type,
    funArgs :: [Arg]
  } deriving (Eq)


instance Show FunType where
  show = identToString . funName


identToString :: Ident -> String
identToString (Ident s) = s


showPos :: BNFC'Position -> String
showPos (Just (x, _)) = " At line: " ++ show x
showPos Nothing = ""


posToStr :: BNFC'Position -> String
posToStr (Just (x, _)) = show x
posToStr Nothing = ""


typeToStr :: Type -> String
typeToStr (Int _) = "'int'"
typeToStr (Bool _) = "'boolean'"
typeToStr (Str _) = "'string'"
typeToStr (Void _) = "'void'"
typeToStr Fun {} = "'fun'"


isVoid :: Type -> Bool
isVoid (Void _) = True
isVoid _        = False


isInt :: Type -> Bool
isInt (Int _) = True
isInt _        = False


isBool :: Type -> Bool
isBool (Bool _) = True
isBool _        = False


isPlus :: AddOp -> Bool
isPlus (Plus _) = True
isPlus (Minus _) = False 


addOpToStr :: AddOp -> String
addOpToStr (Plus _) = "'add'"
addOpToStr (Minus _) = "'sub'" 


mulOpToStr :: MulOp -> String
mulOpToStr (Times _) = "'mul'"
mulOpToStr (Div _) = "'div'" 
mulOpToStr (Mod _) = "'mod'" 


nth :: BNFC'Position
nth = Nothing


typeEquals :: Type -> Type -> Bool
typeEquals (Bool _) (Bool _) = True
typeEquals (Int _) (Int _) = True
typeEquals (Str _) (Str _) = True
typeEquals (Void _) (Void _) = True
typeEquals _ _ = False


isAlwaysTrue :: Expr -> Bool
isAlwaysTrue (ELitTrue pos) = True
isAlwaysTrue _ = False


isAlwaysFalse :: Expr -> Bool
isAlwaysFalse (ELitFalse pos) = True
isAlwaysFalse _ = False
