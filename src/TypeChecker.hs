{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
import Utils
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



type VarTypeEnv = Map.Map Ident Type
type FunTypeEnv = Map.Map Ident FunType
type TypeEnv = (VarTypeEnv, VarTypeEnv, FunTypeEnv)

type IM a = ReaderT TypeEnv (ExceptT String IO) a


initialEnv :: TypeEnv
initialEnv = (Map.empty, Map.empty, mapWithInbuildFunctions)
  where
    mapWithInbuildFunctions = Map.fromList [
      (Ident "printInt", (FunType {
        funName = Ident "printInt",
        funReturnType = Void nth ,
        funArgs = [Arg nth (Int nth) (Ident "argument of function printInt")]})),
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


throwErrorForRelOp :: RelOp -> BNFC'Position -> IM Type
throwErrorForRelOp (EQU _) pos = throwError $ "Type mismatch for '==' operation." ++ showPos pos
throwErrorForRelOp (NE _) pos = throwError $ "Type mismatch for '!=' operation." ++ showPos pos
throwErrorForRelOp (GE _) pos = throwError $ "Type mismatch for '>=' operation." ++ showPos pos
throwErrorForRelOp (LE _) pos = throwError $ "Type mismatch for '<=' operation." ++ showPos pos
throwErrorForRelOp (LTH _) pos = throwError $ "Type mismatch for '<' operation." ++ showPos pos
throwErrorForRelOp (GTH _) pos = throwError $ "Type mismatch for '>' operation." ++ showPos pos


checkArgs :: [Expr] -> [Arg] -> BNFC'Position -> IM TypeEnv
checkArgs [] [] _ = ask
checkArgs (e:exprs) [] pos = throwError $ "Too many function arguments." ++ showPos pos
checkArgs [] (a:args) pos = throwError $ "Too few function arguments." ++ showPos pos
checkArgs (e:exps) ((Arg posA argType id):args) pos = do
  typeOfE <- typeCheckExpr e
  if not $ typeEquals argType typeOfE
    then throwError $ "Wrong type for argument: '" ++ identToString id ++ "'. Expected: " ++ typeToStr argType
              ++ " but found: " ++ typeToStr typeOfE ++ "." ++ showPos pos
    else do
      checkArgs exps args pos


typeCheckExpr :: Expr ->  IM Type
typeCheckExpr (ELitTrue pos) = return $ Bool pos

typeCheckExpr (ELitFalse pos) = return $ Bool pos

typeCheckExpr (ELitInt pos _) = return $ Int pos

typeCheckExpr (EString pos _) = return $ Str pos

typeCheckExpr (EVar pos id) = do
  (vEnvNew, vEnvOld, fEnv) <- ask
  case Map.lookup id vEnvNew of
    Just t -> return t
    Nothing -> case Map.lookup id vEnvOld of
      Just t -> return t
      Nothing -> throwError $ "Use of undefined variable." ++ showPos pos

typeCheckExpr (Neg pos e) = do
  env <- ask
  typeOfE <- typeCheckExpr e
  if isInt typeOfE
    then return $ Int pos
    else throwError $ "Cannot negate a non-integer value." ++ showPos pos

typeCheckExpr (Not pos e) = do
  env <- ask
  typeOfE <- typeCheckExpr e
  if isBool typeOfE
    then return $ Bool pos
    else throwError $ "Cannot execute a 'Not' operation a non-boolean value." ++ showPos pos

typeCheckExpr (EAdd pos e1 op e2) = do
  env <- ask
  typeOfE1 <- typeCheckExpr e1
  typeOfE2 <- typeCheckExpr e2
  case (typeOfE1, typeOfE2) of
    (Int _, Int _) -> return $ Int pos
    (Str _, Str _) -> return $ Str pos
    (Bool _, Bool _) -> throwError $
      "Cannot add boolean values." ++ showPos pos
    (Int _, Str _) -> throwError $
      "Left operand of 'add' operation is an integer and right operand is string." ++ showPos pos
    (Str _, Int _) -> throwError $
      "Left operand of 'add' operation is string and right operand is an integer." ++ showPos pos
    (_, _) -> throwError $
      "Wrong types of operands for 'add' operation." ++ showPos pos

typeCheckExpr (EMul pos e1 op e2) = do
  env <- ask
  typeOfE1 <- typeCheckExpr e1
  typeOfE2 <- typeCheckExpr e2
  if isInt typeOfE1
    then do
      if isInt typeOfE2
        then return $ Int pos
        else throwError $ "Second argument of mul operation is a non-integer value." ++ showPos pos
    else throwError $ "First argument of mul operation is a non-integer value." ++ showPos pos

typeCheckExpr (ERel pos e1 op e2) = do
  env <- ask
  typeOfE1 <- typeCheckExpr e1
  typeOfE2 <- typeCheckExpr e2
  case (typeOfE1, typeOfE2) of
    (Int _, Int _) -> do return $ Bool pos
    (Bool _, Bool _) -> do
      case op of
        (EQU _) -> return $ Bool pos
        (NE _) -> return $ Bool pos
        (GE _) -> throwError $ "Cannot perform '>=' operation on boolean values." ++ showPos pos
        (LE _) -> throwError $ "Cannot perform '<=' operation on boolean values." ++ showPos pos
        (LTH _) -> throwError $ "Cannot perform '<' operation on boolean values." ++ showPos pos
        (GTH _) -> throwError $ "Cannot perform '>' operation on boolean values." ++ showPos pos
    (Str _, Str _) -> do
      case op of
        (EQU _) -> return $ Bool pos
        (NE _) -> return $ Bool pos
        (GE _) -> throwError $ "Cannot perform '>=' operation on strings." ++ showPos pos
        (LE _) -> throwError $ "Cannot perform '<=' operation on strings." ++ showPos pos
        (LTH _) -> throwError $ "Cannot perform '<' operation on strings." ++ showPos pos
        (GTH _) -> throwError $ "Cannot perform '>' operation on strings." ++ showPos pos
    (_, _) -> do throwErrorForRelOp op pos

typeCheckExpr (EAnd pos e1 e2) = do
  env <- ask
  typeOfE1 <- typeCheckExpr e1
  typeOfE2 <- typeCheckExpr e2
  if isBool typeOfE1
    then do
      if isBool typeOfE2
        then return $ Bool pos
        else throwError $ "Second argument of 'and' operation is a non-boolean value." ++ showPos pos
    else throwError $ "First argument of 'and' operation is a non-boolean value." ++ showPos pos

typeCheckExpr (EOr pos e1 e2) = do
  env <- ask
  typeOfE1 <- typeCheckExpr e1
  typeOfE2 <- typeCheckExpr e2
  if isBool typeOfE1
    then do
      if isBool typeOfE2
        then return $ Bool pos
        else throwError $ "Second argument of 'or' operation is a non-boolean value." ++ showPos pos
    else throwError $ "First argument of 'or' operation is a non-boolean value." ++ showPos pos

typeCheckExpr (EApp pos id exprs) = do
  (_, _, fEnv) <- ask
  case Map.lookup id fEnv of
    Just (FunType name funRetType arguments) -> do
      checkArgs exprs arguments pos
      return funRetType
    Nothing -> throwError $ "Use of undefined function " ++ identToString id ++ "." ++ showPos pos


checkTypeForId :: Ident -> BNFC'Position -> IM Type
checkTypeForId id pos = do
  (vEnvNew, vEnvOld, fEnv) <- ask
  case Map.lookup id vEnvNew of
    Nothing -> case Map.lookup id vEnvOld of
      Nothing -> throwError $ "Use of undefined variable: " ++ identToString id ++ "." ++ showPos pos
      Just t -> return t
    Just t -> return t


typeCheckStmt :: Stmt -> Type -> IM (TypeEnv, WasThereAReturn)
typeCheckStmt (Empty _) _ = do
  env <- ask
  return (env, False)

typeCheckStmt (Ass pos id e) _ = do
  expectedTypeOfVar <- checkTypeForId id pos
  typeOfExpr <- typeCheckExpr e
  if typeEquals typeOfExpr expectedTypeOfVar
    then do
      env <- ask
      return (env, False)
    else throwError $ "Cannot assign type " ++ typeToStr typeOfExpr
                ++ " to variable of type " ++ typeToStr expectedTypeOfVar ++ "." ++ showPos pos

typeCheckStmt (Incr pos id) t = do
  typeOfVar <- checkTypeForId id pos
  if not $ isInt typeOfVar
    then throwError $ "Cannot increment non-integer value." ++ showPos pos
    else do
      env <- ask
      return (env, False)

typeCheckStmt (Decr pos id) t = do
  typeOfVar <- checkTypeForId id pos
  if not $ isInt typeOfVar
    then throwError $ "Cannot decrement non-integer value." ++ showPos pos
    else do
      env <- ask
      return (env, False)

typeCheckStmt (Ret pos e) expectedRetType = do
  if isVoid expectedRetType
    then throwError $ "Cannot return value from void function." ++ showPos pos
    else do
      env <- ask
      actualTypeOfExpr <- typeCheckExpr e
      if not $ typeEquals actualTypeOfExpr expectedRetType
        then throwError $ "Return type mismatch: Expected " ++ typeToStr expectedRetType
                        ++ ", but found " ++ typeToStr actualTypeOfExpr ++ "." ++ showPos pos
        else return (env, True)

typeCheckStmt (VRet pos) expectedRetType = do
  if not $ isVoid expectedRetType
    then throwError $ "A non-void function must return a value." ++ showPos pos
    else do
      env <- ask
      return (env, True)

typeCheckStmt (Cond pos condExpr stmt) t = do
  env <- ask
  typeOfExpr <- typeCheckExpr condExpr
  if not $ isBool typeOfExpr
    then throwError $ "Condition has to be boolean." ++ showPos pos
    else do
      (_, wasThereReturn) <- typeCheckStmt stmt t
      if isAlwaysTrue condExpr
        then return (env, wasThereReturn)
        else return (env, False)

typeCheckStmt (CondElse pos condExpr stmtTrue stmtFalse) t = do
  env <- ask
  typeOfExpr <- typeCheckExpr condExpr
  if not $ isBool typeOfExpr
    then throwError $ "Condition has to be boolean." ++ showPos pos
    else do
      (_, wasThereRetunInT) <- local (const env) $ typeCheckStmt stmtTrue t
      (_, wasThereRetunInF) <- local (const env) $ typeCheckStmt stmtFalse t
      if isAlwaysTrue condExpr
        then return (env, wasThereRetunInT)
        else do
          if isAlwaysFalse condExpr
            then return (env, wasThereRetunInF)
            else return (env, wasThereRetunInT && wasThereRetunInF)

typeCheckStmt (SExp pos e) t = do
  env <- ask
  typeCheckExpr e
  return (env, False)

typeCheckStmt (While pos condExpr stmt) t = do
  env <- ask
  typeOfExpr <- typeCheckExpr condExpr
  if not $ isBool typeOfExpr
    then throwError $ "Condition has to be boolean." ++ showPos pos
    else do
      (_, wasThereReturn) <- typeCheckStmt stmt t
      if isAlwaysTrue condExpr
        then return (env, wasThereReturn)
        else return (env, False)

typeCheckStmt (BStmt pos (Block posB stmts)) t = do
  (vEnvNew, vEnvOld, fEnv) <- ask
  let newEnvOld = Map.union vEnvNew vEnvOld
  (_, wasReturn) <- local (const (Map.empty, newEnvOld, fEnv)) $ typeCheckStmts stmts t
  return ((vEnvNew, vEnvOld, fEnv), wasReturn) --zwracamy środowisko niezmienione

typeCheckStmt (Decl pos t []) typ = do
  throwError "Wrong declaration."
typeCheckStmt (Decl pos t items) typ = do
  if isVoid t
    then throwError $ "Cannot create variable of type void." ++ showPos pos
    else do
      env' <- typeCheckDecls items t
      return (env', False)


typeCheckDecls :: [Item] -> Type -> IM TypeEnv
typeCheckDecls [] _ = ask

typeCheckDecls (Init  pos id e : items) t = do
  (vEnvNew, vEnvOld, fEnv) <- ask
  case Map.lookup id vEnvNew of
    Just _ -> throwError $ "Multiple declaration of variable '" ++ identToString id ++ "'." ++ showPos pos
    Nothing -> do
      case Map.lookup id fEnv of
        Just _ -> throwError $ "Cannot declare a variable of name '" ++ identToString id
                  ++ "' because a function of that name already exists.." ++ showPos pos
        Nothing -> do
          typeOfExpr <- typeCheckExpr e
          if typeEquals typeOfExpr t
            then do
              let env' = (Map.insert id t vEnvNew, vEnvOld, fEnv)
              local (const env') $ typeCheckDecls items t
            else throwError $ "Cannot assign type " ++ typeToStr typeOfExpr
                            ++ " to variable of type " ++ typeToStr t ++ "." ++ showPos pos

typeCheckDecls (NoInit  pos id : items) t = do
  (vEnvNew, vEnvOld, fEnv) <- ask
  case Map.lookup id vEnvNew of
    Just _ -> throwError $ "Multiple declaration of variable '" ++ identToString id ++ "'." ++ showPos pos
    Nothing -> do
      case Map.lookup id fEnv of
        Just _ -> throwError $ "Cannot declare a variable of name '" ++ identToString id
                  ++ "' because a function of that name already exists.." ++ showPos pos
        Nothing -> do
          let env' = (Map.insert id t vEnvNew, vEnvOld, fEnv)
          local (const env') $ typeCheckDecls items t


typeCheckStmts :: [Stmt] -> Type -> IM (TypeEnv, WasThereAReturn)
typeCheckStmts [] _ = do
  env <- ask
  return (env, False)
typeCheckStmts [stmt] t  = do
  env <- ask
  (env', wasReturn) <- local (const env) $ typeCheckStmt stmt t
  return (env', wasReturn)
typeCheckStmts (stmt : rest) t = do
  (env', wasReturnInFirst) <- typeCheckStmt stmt t
  (env'', wasReturnInRest) <- local (const env') $ typeCheckStmts rest t
  return (env'', wasReturnInFirst || wasReturnInRest)


addArgsToEnv :: [Arg] -> IM TypeEnv
addArgsToEnv [] = ask
addArgsToEnv ((Arg pos argType id):args) = do
  (vEnvNew, vEnvOld, fEnv) <- ask
  case Map.lookup id vEnvNew of
    Just _ -> throwError $ "Several arguments with the same name: '" ++ identToString id ++ "'." ++ showPos pos
    Nothing -> do
      case Map.lookup id fEnv of
        Just _ -> throwError $ "Cannot name an argument with the name of an existing function: '"
                      ++ identToString id ++ "'." ++ showPos pos
        Nothing -> do
          let env' = (Map.insert id argType vEnvNew, vEnvOld, fEnv)
          local (const env') $ addArgsToEnv args


typeCheckTopDef :: TopDef -> IM TypeEnv
typeCheckTopDef (FnDef pos t id args (Block posB stmts)) = do
  env' <- addArgsToEnv args
  (env'', wasReturn) <- local (const env') $ typeCheckStmts stmts t
  if not wasReturn && not (isVoid t)
    then throwError $ "No return in function " ++ identToString id
    else return env''


typeCheckTopDefs :: [TopDef] -> IM TypeEnv
typeCheckTopDefs [] = ask
typeCheckTopDefs (def : restDefs) = do
  (_, _, _) <- typeCheckTopDef def
  --Wywołujemy z envem lokalnym, żeby zmienne deklarowane 
  --w funkcji nie były widoczne w kolejnych funkcjach.
  typeCheckTopDefs restDefs


addAllFunctionsToEnv :: [TopDef] -> IM TypeEnv
addAllFunctionsToEnv [] = ask
addAllFunctionsToEnv ((FnDef pos t id args (Block posB stmts)): restDefs) = do
  (vEnvNew, vEnvOld, fEnv) <- ask
  case Map.lookup id fEnv of
    Just _ -> throwError $ "Multiple declaration of function " ++ identToString id ++ "." ++ showPos pos
    Nothing -> do
      let env' = (vEnvNew, vEnvOld, Map.insert id (FunType {funName = id, funReturnType = t, funArgs = args}) fEnv)
      local (const env') $ addAllFunctionsToEnv restDefs


typeCheckProgram :: Program -> IM TypeEnv
typeCheckProgram (Program pos []) =
  throwError "No main() function"
typeCheckProgram (Program pos topdefs) = do
  (vEnvNew', vEnvOld', fEnv') <- addAllFunctionsToEnv topdefs
  case Map.lookup (Ident "main") fEnv' of
    Nothing -> throwError "No main() function"
    Just FunType {funName = id, funReturnType = t, funArgs = args} -> do
      case t of
        Int _ -> do 
          case args of 
            [] ->  local (const (vEnvNew', vEnvOld', fEnv')) $ typeCheckTopDefs topdefs
            _ -> throwError "The argument list of the main() function is non-empty"
        _ -> throwError "Wrong return type for function main()"


parse :: String -> Either String Program
parse input =
  case pProgram (myLexer input) of
    Ok program -> Right program
    Bad err -> Left err


runMonad :: IM a -> TypeEnv -> IO (Either String a)
runMonad checker env = runExceptT (runReaderT checker env)


handleInput :: FilePath -> String -> IO ()
handleInput filename input = do
  case parse input of
    Left err -> do
      hPutStrLn stderr $ "ERROR:\n" ++ "Syntax error in file: " ++ filename ++ ": " ++ err
      exitFailure
    Right code -> do
      let result = runMonad (typeCheckProgram code) initialEnv
      resultWithIo <- liftIO result
      case resultWithIo of
        Left errMsg -> hPutStrLn stderr $ "ERROR:\n" ++ errMsg ++ "."
        Right env -> hPutStrLn stderr "OK"


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
