{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant return" #-}
{-# HLINT ignore "Eta reduce" #-}
{-# HLINT ignore "Use print" #-}
import LexLatte
import ParLatte
import AbsLatte
import ErrM
import System.Environment
import Control.Monad
import Text.Printf
import System.Exit
import System.IO
import System.Directory
import Control.Exception (catch, IOException, throw)
import qualified Data.Map as Map
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Class



data FunType = FunType
  { funName :: Ident,
    funReturnType :: Type,
    funArgs :: [Arg],
    funBlock :: Block,
    funPos :: BNFC'Position
  } deriving (Eq)


identToString :: Ident -> String
identToString (Ident s) = s


instance Show FunType where
  show = identToString . funName


data Value = VInt Integer | VBool Bool | VString String | VVoid | VFun FunType


instance Show Value where
  show (VInt i) = show i
  show (VBool b) = show b
  show (VString s) = s
  show VVoid = "void"
  show (VFun f) = show f



posToStr :: BNFC'Position -> String
posToStr (Just (x, _)) = show x
posToStr Nothing = "Nothing"

isVoid :: Type -> Bool
isVoid (Void _) = True
isVoid _        = False

isInt :: Type -> Bool
isInt (Int _) = True
isInt _        = False

isBool :: Type -> Bool
isBool (Bool _) = True
isBool _        = False


type Var = Ident
type WasThereAReturn = Bool

type TypeEnv = Map.Map Var Type
type ErrorList = [String]
type IM a = ReaderT TypeEnv (ExceptT ErrorList IO) a


runMonad :: IM a -> TypeEnv -> IO (Either ErrorList a)
runMonad checker env = runExceptT (runReaderT checker env)

typeEquals :: Type -> Type -> Bool
typeEquals (Bool _) (Bool _) = True
typeEquals (Int _) (Int _) = True
typeEquals (Str _) (Str _) = True
typeEquals (Void _) (Void _) = True
typeEquals _ _ = False  -- For other types, assuming they're not equal


throwErrorForRelOp :: RelOp -> BNFC'Position -> IM Type
throwErrorForRelOp (EQU _) pos = throwError ["Type mismatch for '==' operation at line " ++ posToStr pos]
throwErrorForRelOp (NE _) pos = throwError ["Type mismatch for '!=' operation at line " ++ posToStr pos]
throwErrorForRelOp (GE _) pos = throwError ["Type mismatch for '>=' operation at line " ++ posToStr pos]
throwErrorForRelOp (LE _) pos = throwError ["Type mismatch for '<=' operation at line " ++ posToStr pos]
throwErrorForRelOp (LTH _) pos = throwError ["Type mismatch for '<' operation at line " ++ posToStr pos]
throwErrorForRelOp (GTH _) pos = throwError ["Type mismatch for '>' operation at line " ++ posToStr pos]

typeCheckExpr :: Expr ->  IM Type
typeCheckExpr (ELitTrue pos) = return $ Bool pos
typeCheckExpr (ELitFalse pos) = return $ Bool pos
typeCheckExpr (ELitInt pos _) = return $ Int pos
typeCheckExpr (EString pos _) = return $ Str pos
typeCheckExpr (EVar pos id) = do
  env <- ask
  case Map.lookup id env of
    Just t -> return t
    Nothing -> throwError ["Use of uninitialised variable at line " ++ posToStr pos]
typeCheckExpr (Neg pos e) = do 
  env <- ask
  typeOfE <- typeCheckExpr e
  if isInt typeOfE 
    then return $ Int pos
    else throwError ["Cannot negate a non-integer value at line " ++ posToStr pos]
typeCheckExpr (Not pos e) = do 
  env <- ask
  typeOfE <- typeCheckExpr e
  if isBool typeOfE 
    then return $ Bool pos
    else throwError ["Cannot execute a 'Not' operation a non-boolean value at line " ++ posToStr pos]
typeCheckExpr (EAdd pos e1 op e2) = do 
  env <- ask
  typeOfE1 <- typeCheckExpr e1
  typeOfE2 <- typeCheckExpr e2
  if isInt typeOfE1 
    then do 
      if isInt typeOfE2 
        then return $ Int pos
        else throwError ["Second argument of add operation is a non-integer value at line " ++ posToStr pos]
    else throwError ["First argument of add operation is a non-integer value at line " ++ posToStr pos]
typeCheckExpr (EMul pos e1 op e2) = do 
  env <- ask
  typeOfE1 <- typeCheckExpr e1
  typeOfE2 <- typeCheckExpr e2
  if isInt typeOfE1 
    then do 
      if isInt typeOfE2 
        then return $ Int pos
        else throwError ["Second argument of mul operation is a non-integer value at line " ++ posToStr pos]
    else throwError ["First argument of mul operation is a non-integer value at line " ++ posToStr pos]
typeCheckExpr (ERel pos e1 op e2) = do 
  env <- ask
  typeOfE1 <- typeCheckExpr e1
  typeOfE2 <- typeCheckExpr e2
  case (typeOfE1, typeOfE2) of
    (Int _, Int _) -> do return $ Bool pos --dla intów każda operacja jest okej
    (Bool _, Bool _) -> do 
      case op of 
        (EQU _) -> return $ Bool pos
        (NE _) -> return $ Bool pos
        (GE _) -> throwError ["Cannot perform '>=' operation on boolean values at line " ++ posToStr pos]
        (LE _) -> throwError ["Cannot perform '<=' operation on boolean values at line " ++ posToStr pos]
        (LTH _) -> throwError ["Cannot perform '<' operation on boolean values at line " ++ posToStr pos]
        (GTH _) -> throwError ["Cannot perform '>' operation on boolean values at line " ++ posToStr pos]
    (Str _, Str _) -> do 
      case op of 
        (EQU _) -> return $ Bool pos
        (NE _) -> return $ Bool pos
        (GE _) -> throwError ["Cannot perform '>=' operation on strings at line " ++ posToStr pos]
        (LE _) -> throwError ["Cannot perform '<=' operation on strings at line " ++ posToStr pos]
        (LTH _) -> throwError ["Cannot perform '<' operation on strings at line " ++ posToStr pos]
        (GTH _) -> throwError ["Cannot perform '>' operation on strings at line " ++ posToStr pos]
    (_, _) -> do throwErrorForRelOp op pos
typeCheckExpr (EAnd pos e1 e2) = do 
  env <- ask
  typeOfE1 <- typeCheckExpr e1
  typeOfE2 <- typeCheckExpr e2
  if isBool typeOfE1 
    then do 
      if isBool typeOfE2 
        then return $ Bool pos
        else throwError ["Second argument of 'and' operation is a non-boolean value at line " ++ posToStr pos]
    else throwError ["First argument of 'and' operation is a non-boolean value at line " ++ posToStr pos]
typeCheckExpr (EOr pos e1 e2) = do 
  env <- ask
  typeOfE1 <- typeCheckExpr e1
  typeOfE2 <- typeCheckExpr e2
  if isBool typeOfE1 
    then do 
      if isBool typeOfE2 
        then return $ Bool pos
        else throwError ["Second argument of 'or' operation is a non-boolean value at line " ++ posToStr pos]
    else throwError ["First argument of 'or' operation is a non-boolean value at line " ++ posToStr pos]
typeCheckExpr (EApp pos id exprs) = do return $ Bool pos


typeCheckStmt :: Stmt -> Type -> IM (TypeEnv, WasThereAReturn)
typeCheckStmt (Empty _) t = do
  env <- ask
  return (env, False)
typeCheckStmt (Ass pos x e) t = do
  env <- ask
  case Map.lookup x env of
    Nothing -> throwError ["Uninitialised varaible at line " ++ posToStr pos] 
    Just _ -> do
      typeOfExpr <- typeCheckExpr e
      if typeEquals typeOfExpr t
        then do
          --env' <- Map.insert x t env -- Update the environment
          return (Map.insert x t env, False)
        else throwError ["Type mismatch at line " ++ show pos]

typeCheckStmt (Incr pos x) t = do
  env <- ask
  return (env, False)
typeCheckStmt (Decr pos x) t = do
  env <- ask
  return (env, False)
typeCheckStmt (Ret pos e) t = do
  env <- ask
  return (env, True)
--trzeba sprawdzić czy typ e jest taki jaki mmay zwrócić
typeCheckStmt (VRet pos) t = do
  env <- ask
  return (env, True)
--powinniśmy być w funkcji typu void
--jeśli nie to rzucić error że nie zwracamy wartości w funkcji która powinna zwracać typ ...
typeCheckStmt (Cond pos condition block) t = do
  env <- ask
  return (env, False)
typeCheckStmt (CondElse pos condExpr stmtTrue stmtFalse) t = do
  env <- ask
  return (env, False)
typeCheckStmt (SExp pos e) t = do
  env <- ask
  return (env, False)
typeCheckStmt (While pos cond stmt) t = do
  env <- ask
  return (env, False)
typeCheckStmt (BStmt pos block) t = do
  env <- ask
  return (env, False)
typeCheckStmt (Decl pos t []) typ = do
  throwError ["wrong decl"]
typeCheckStmt (Decl pos t items) typ = do
  if isVoid t
    then throwError ["Cannot create variable of type void at line " ++ posToStr pos] 
    else do
      env' <- typeCheckDecls items t
      return (env', False)


typeCheckDecls :: [Item] -> Type -> IM TypeEnv
typeCheckDecls [Init  pos id e] t = do
  env <- ask
  typeOfExpr <- typeCheckExpr e
  if typeEquals typeOfExpr t
    then do
      --env' <- Map.insert x t env -- Update the environment
      return $ Map.insert id t env
    else throwError ["Type mismatch at line " ++ posToStr pos]
typeCheckDecls (Init  pos id e : items) t = do
  env <- ask
  typeOfExpr <- typeCheckExpr e
  if typeEquals typeOfExpr t
    then do
      let env' = Map.insert id t env
      env'' <- local (const env') $ typeCheckDecls items t
      return env''
    else throwError ["Type mismatch at line " ++ posToStr pos]
typeCheckDecls [NoInit  pos id] t = do
  env <- ask
  --trzeba sprawdzic czy nie ma już takiej zmiennej
  return $ Map.insert id t env
typeCheckDecls (NoInit  pos id : items) t = do
  env <- ask
  --trzeba sprawdzic czy nie ma już takiej zmiennej
  let env' = Map.insert id t env
  env'' <- local (const env') $ typeCheckDecls items t
  return env''




typeCheckStmts :: [Stmt] -> Type -> IM TypeEnv
--typeCheckStmts stmts = do
  --mapM_ typeCheckStmt stmts -- Assuming typeCheckStmt is defined to handle single statements
  --ask -- Return the current environment after type checking
typeCheckStmts [] _ = ask
typeCheckStmts [stmt] t = do  -- Case for a single statement
  env <- ask
  (env', wasReturn) <- local (const env) $ typeCheckStmt stmt t
  if not wasReturn
    then throwError ["No return."]
    --uwaga tutaj zwracam enva otrzymanefo z typeCheckStmt
    else return env'
typeCheckStmts (stmt : rest) t = do  -- Recursive case for multiple statements
  env <- ask
  (env', wasReturn) <- local (const env) $ typeCheckStmt stmt t
  if wasReturn
    then throwError ["Return must be the last instruction in function."]
    else do
      env'' <- local (const env') $ typeCheckStmts rest t
      --uwaga tutaj zwracam enva tego otrzymanefo z typeCheckStmt
      return env''


-- FnDef a (Type' a) Ident [Arg' a] (Block' a)
-- GVarDecl a (Type' a) [Item' a]
-- GVarInit a Ident (Expr' a)

typeCheckTopDef :: TopDef -> IM TypeEnv
typeCheckTopDef (FnDef pos t id args (Block posB stmts)) = do
  typeCheckStmts stmts t
  env <- ask
  return env
typeCheckTopDef (GVarDecl pos t items) = do
  env <- ask
  return env
typeCheckTopDef (GVarInit pos id expr) = do
  env <- ask
  return env

typeCheckProgram :: Program -> IM TypeEnv
typeCheckProgram (Program pos []) =
  --istnieje szansa, że my w ogóle nie chcemy tego błęu wykrywać na poziomie frontendu
  --i tutaj chcemy po prostu zwrócić env albo w ogóle nie robić tego przypadku
  throwError ["No main() function."]
typeCheckProgram (Program pos topDefs) = do
  mapM_ typeCheckTopDef topDefs -- Apply typeCheckTopDef to each TopDef
  env <- ask -- Retrieve the final environment after type checking
  return env
--wersja z rekursją
--typeCheckProgram (Program pos (def : restDefs)) = do
  --  typeCheckTopDef def -- Apply type checking to the current TopDef
    --typeCheckProgram (Program pos restDefs) -- Recur with the remaining TopDefs


parse :: String -> Either String Program
parse input =
  case pProgram (myLexer input) of
    Ok program -> Right program
    Bad err -> Left err


initialEnv :: TypeEnv
initialEnv = Map.empty


handleInput :: FilePath -> String -> IO ()
handleInput filename input = do
  case parse input of
    Left err -> do
      hPutStrLn stderr $ "Syntax error in file: " ++ filename ++ ": " ++ err
      exitFailure
    Right code -> do
      --print code
      let result = runMonad (typeCheckProgram code) initialEnv
      resultWithIo <- liftIO result
      case resultWithIo of
        Left errMsg -> putStrLn $ "Error: " ++ unlines errMsg
        Right env -> putStrLn "TypeCheck successful :)"


main :: IO ()
main = do
  args <- getArgs
  case args of
    [filename] -> do
      input <- readFile filename
      handleInput filename input
    _ -> do
      hPutStrLn stderr "Usage: ./insc program"
      exitFailure
