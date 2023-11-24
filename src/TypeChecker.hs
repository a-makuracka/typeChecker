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
import GHC.Exts.Heap (GenClosure(n_args))



data FunType = FunType
  { funName :: Ident,
    funReturnType :: Type,
    funArgs :: [Arg]
    --funPos :: BNFC'Position
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

typeToStr :: Type -> String
typeToStr (Int _) = "int"
typeToStr (Bool _) = "boolean"
typeToStr (Str _) = "string"
typeToStr (Void _) = "void"


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
type IsFun = Bool

type VarTypeEnv = Map.Map Var Type
type FunTypeEnv = Map.Map Ident FunType
type TypeEnv = (VarTypeEnv, FunTypeEnv)
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


typeEqualsForArgs :: Arg -> Type -> Bool
typeEqualsForArgs (Arg pos argType id) expectedType = typeEquals argType expectedType


checkArgs :: [Expr] -> [Arg] -> BNFC'Position -> IM TypeEnv
checkArgs [] [] _ = ask
checkArgs (e:exprs) [] pos = throwError ["To many function arguments at line: " ++ posToStr pos]
checkArgs [] (a:args) pos = throwError ["To little function arguemnts at line: " ++ posToStr pos]
checkArgs (e:exps) ((Arg posA argType id):args) pos = do
  typeOfE <- typeCheckExpr e
  if not $ typeEquals argType typeOfE
    then throwError ["Wrong type for argument: '" ++ identToString id ++ "'. Expected: '" ++ typeToStr argType
    ++ "' but found: '" ++ typeToStr typeOfE ++ "' at line: " ++ posToStr pos]
    else do
      (vEnv, fEnv) <- ask
      checkArgs exps args pos


typeCheckExpr :: Expr ->  IM Type
typeCheckExpr (ELitTrue pos) = return $ Bool pos
typeCheckExpr (ELitFalse pos) = return $ Bool pos
typeCheckExpr (ELitInt pos _) = return $ Int pos
typeCheckExpr (EString pos _) = return $ Str pos
typeCheckExpr (EVar pos id) = do
  (vEnv, fEnv) <- ask
  case Map.lookup id vEnv of
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
typeCheckExpr (EApp pos id exprs) = do
  (vEnv, fEnv) <- ask
  case Map.lookup id fEnv of
    Just (FunType name funRetType arguments) -> do
      checkArgs exprs arguments pos
      return funRetType
    Nothing -> throwError ["Use of uninitialised function " ++ identToString id ++ " at line " ++ posToStr pos]



typeCheckStmt :: Stmt -> Type -> IM (TypeEnv, WasThereAReturn)
typeCheckStmt (Empty _) _ = do
  env <- ask
  return (env, False)
typeCheckStmt (Ass pos id e) _ = do
  (vEnv, fEnv) <- ask
  case Map.lookup id vEnv of
    Nothing -> throwError ["Uninitialized variable at line " ++ posToStr pos]
    Just t -> do
      typeOfExpr <- typeCheckExpr e
      if typeEquals typeOfExpr t
        then do
          --return ((Map.insert id t vEnv, fEnv), False)
          return ((vEnv, fEnv), False)
        else throwError ["Cannot assign type " ++ typeToStr typeOfExpr
                    ++ " to variable of type " ++ typeToStr t ++ " at line " ++ posToStr pos]
typeCheckStmt (Incr pos id) t = do
  (vEnv, fEnv) <- ask
  case Map.lookup id vEnv of
    Nothing -> throwError ["Uninitialized variable at line " ++ posToStr pos]
    Just typeOfVar -> do
      if not $ isInt typeOfVar
        then throwError ["Cannot increment non-integer value at line " ++ posToStr pos]
        else return ((vEnv, fEnv), False)
typeCheckStmt (Decr pos id) t = do
  (vEnv, fEnv) <- ask
  case Map.lookup id vEnv of
    Nothing -> throwError ["Uninitialized variable at line " ++ posToStr pos]
    Just typeOfVar -> do
      if not $ isInt typeOfVar
        then throwError ["Cannot decrement non-integer value at line " ++ posToStr pos]
        else return ((vEnv, fEnv), False)
typeCheckStmt (Ret pos e) expectedRetType = do
  if isVoid expectedRetType
    then throwError ["Cannot return value from void function at line " ++ posToStr pos]
    else do
      env <- ask
      actualTypeOfExpr <- typeCheckExpr e
      if not $ typeEquals actualTypeOfExpr expectedRetType
        then throwError ["Return type mismatch: Expected " ++ typeToStr expectedRetType
                        ++ ", but found " ++ typeToStr actualTypeOfExpr ++ " at line " ++ posToStr pos]
        else return (env, True)
typeCheckStmt (VRet pos) expectedRetType = do
  if not $ isVoid expectedRetType
    then throwError ["A non-void function must return a value. At line: " ++ posToStr pos]
    else do
      env <- ask
      return (env, True)
typeCheckStmt (Cond pos condExpr stmt) t = do
  env <- ask
  typeOfExpr <- typeCheckExpr condExpr
  if not $ isBool typeOfExpr
    then throwError ["Condition has to be boolean at line " ++ posToStr pos]
    else do
      (_, _) <- typeCheckStmt stmt t
      return (env, False)
typeCheckStmt (CondElse pos condExpr stmtTrue stmtFalse) t = do
  env <- ask
  typeOfExpr <- typeCheckExpr condExpr
  if not $ isBool typeOfExpr
    then throwError ["Condition has to be boolean at line " ++ posToStr pos]
    else do
      (_, wasThereRetunInT) <- local (const env) $ typeCheckStmt stmtTrue t
      (_, wasThereRetunInF) <- local (const env) $ typeCheckStmt stmtFalse t
      return (env, wasThereRetunInT && wasThereRetunInF)
typeCheckStmt (SExp pos e) t = do
  env <- ask
  typeCheckExpr e
  return (env, False)
typeCheckStmt (While pos condExpr stmt) t = do
  env <- ask
  typeOfExpr <- typeCheckExpr condExpr
  if not $ isBool typeOfExpr
    then throwError ["Condition has to be boolean at line " ++ posToStr pos]
    else do
      (_, _) <- typeCheckStmt stmt t
      return (env, False)
typeCheckStmt (BStmt pos (Block posB stmts)) t = do
  env <- ask
  (env', wasReturn) <- typeCheckStmts stmts t
  return (env, wasReturn)
typeCheckStmt (Decl pos t []) typ = do
  throwError ["Wrong declaration."]
typeCheckStmt (Decl pos t items) typ = do
  if isVoid t
    then throwError ["Cannot create variable of type void at line " ++ posToStr pos]
    else do
      env' <- typeCheckDecls items t
      return (env', False)


typeCheckDecls :: [Item] -> Type -> IM TypeEnv
typeCheckDecls [] _ = ask
typeCheckDecls (Init  pos id e : items) t = do
  (vEnv, fEnv) <- ask
  case Map.lookup id vEnv of 
    Just _ -> throwError ["Multiple declaration of variable '" ++ identToString id ++ "' at line: " ++ posToStr pos]
    Nothing -> do
      case Map.lookup id fEnv of
        Just _ -> throwError ["Cannot declare a variable of name '" ++ identToString id 
                  ++ "' because a function of that name already exists. At line: " ++ posToStr pos]
        Nothing -> do
          typeOfExpr <- typeCheckExpr e
          if typeEquals typeOfExpr t
            then do
              let env' = (Map.insert id t vEnv, fEnv)
              env'' <- local (const env') $ typeCheckDecls items t
              return env''
            else throwError ["Cannot assign type " ++ typeToStr typeOfExpr
                            ++ " to variable of type " ++ typeToStr t ++ " at line: " ++ posToStr pos]
typeCheckDecls (NoInit  pos id : items) t = do
  (vEnv, fEnv) <- ask
  case Map.lookup id vEnv of 
    Just _ -> throwError ["Multiple declaration of variable '" ++ identToString id ++ "' at line: " ++ posToStr pos]
    Nothing -> do
      case Map.lookup id fEnv of
        Just _ -> throwError ["Cannot declare a variable of name '" ++ identToString id 
                  ++ "' because a function of that name already exists. At line: " ++ posToStr pos]
        Nothing -> do
          let env' = (Map.insert id t vEnv, fEnv)
          env'' <- local (const env') $ typeCheckDecls items t
          return env''


typeCheckStmts :: [Stmt] -> Type -> IM (TypeEnv, WasThereAReturn)
typeCheckStmts [] _ = do
  env <- ask
  return (env, False)
typeCheckStmts [stmt] t  = do
  env <- ask
  (env', wasReturn) <- local (const env) $ typeCheckStmt stmt t
  return (env', wasReturn)
typeCheckStmts (stmt : rest) t = do
  (vEnv, fEnv) <- ask
  (env', wasReturnInFirst) <- local (const (vEnv, fEnv)) $ typeCheckStmt stmt t
  (env'', wasReturnInRest) <- local (const env') $ typeCheckStmts rest t
  return (env'', wasReturnInFirst || wasReturnInRest)


addArgsToEnv :: [Arg] -> IM TypeEnv
addArgsToEnv [] = ask
addArgsToEnv ((Arg pos argType id):args) = do
  (vEnv, fEnv) <- ask
  case Map.lookup id vEnv of 
    Just _ -> throwError ["Several arguments with the same name: '" ++ identToString id ++ "' at line: " ++ posToStr pos]
    Nothing -> do
      case Map.lookup id fEnv of
        Just _ -> throwError ["Cannot name an argument with the name of an existing function: '" 
                      ++ identToString id ++ "' At line: " ++ posToStr pos]
        Nothing -> do
          let env' = (Map.insert id argType vEnv, fEnv)
          env'' <- local (const env') $ addArgsToEnv args
          return env''


typeCheckTopDef :: TopDef -> IM TypeEnv
typeCheckTopDef (FnDef pos t id args (Block posB stmts)) = do
  (vEnv, fEnv) <- ask
  let env' = (vEnv, Map.insert id (FunType {funName = id, funReturnType = t, funArgs = args}) fEnv)
  env'' <- local (const env') $ addArgsToEnv args
  (env''', wasReturn) <- local (const env'') $ typeCheckStmts stmts t
  if not wasReturn
    then throwError ["no return in function " ++ show id]
    else return env'''


typeCheckTopDefs :: [TopDef] -> IM TypeEnv
typeCheckTopDefs [def] = do
  env' <- typeCheckTopDef def
  return env'
typeCheckTopDefs (def : restDefs) = do
  (vEnv, fEnv) <- ask
  (vEnv', fEnv') <- typeCheckTopDef def
  --chcemy żeby kolejna funkcja widziała wyżej zadeklarowane funkcje, ale nie widziała deklarowanych w nich zmiennych
  env'' <- local (const (vEnv, fEnv')) $ typeCheckTopDefs restDefs
  return env''


typeCheckProgram :: Program -> IM TypeEnv
typeCheckProgram (Program pos []) =
  --istnieje szansa, że my w ogóle nie chcemy tego błęu wykrywać na poziomie frontendu
  --i tutaj chcemy po prostu zwrócić env albo w ogóle nie robić tego przypadku
  throwError ["No main() function."]
--typeCheckProgram (Program pos topDefs) = do
  --mapM_ typeCheckTopDef topDefs -- Apply typeCheckTopDef to each TopDef
  --env <- ask -- Retrieve the final environment after type checking
  --return env
--wersja z rekursją
typeCheckProgram (Program pos topdefs) = do
    typeCheckTopDefs topdefs


parse :: String -> Either String Program
parse input =
  case pProgram (myLexer input) of
    Ok program -> Right program
    Bad err -> Left err


nth :: BNFC'Position
nth = Nothing


initialEnv :: TypeEnv
initialEnv = (Map.empty, mapWithInbuildFunctions)
  where
    mapWithInbuildFunctions = Map.fromList [
      (Ident "printInt", (FunType {
        funName = Ident "printInt", 
        funReturnType = Void nth , 
        funArgs = [Arg nth (Int nth) (Ident "argumrnt of function printInt")]})),
      (Ident "printString", (FunType {
        funName = Ident "printString", 
        funReturnType = Void nth , 
        funArgs = [Arg nth (Str nth) (Ident "argument of function printString")]})),
      (Ident "error", (FunType {
        funName = Ident "error", 
        funReturnType = Void nth , 
        funArgs = []})),
      (Ident "readInt", (FunType {
        funName = Ident "readInt", 
        funReturnType = Int nth , 
        funArgs = []})),
      (Ident "readString", (FunType {
        funName = Ident "readString", 
        funReturnType = Str nth , 
        funArgs = []}))
      ]

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
