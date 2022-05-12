import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Control.Monad.State.Lazy 
import System.IO
import System.Environment

type VarId = String
data Expr = CInt Int
          | CBool Bool
          | Var VarId
          | Plus Expr Expr
          | Minus Expr Expr
          | Equal Expr Expr
          | ITE Expr Expr Expr
          | Abs VarId Expr
          | App Expr Expr
          | LetIn VarId Expr Expr
          deriving (Eq, Ord, Read, Show)
data Type = TInt
          | TBool
          | TError
          | TVar Int
          | TArr Type Type
          deriving (Eq, Ord, Read, Show)
data Constraint = CEq Type Type
                | CError
                deriving (Eq, Ord, Read, Show)
type ConstraintSet = Set.Set Constraint
type ConstraintList = [Constraint]
type Env = Map.Map VarId Type
type InferState a = State Int a
type Substitution = Map.Map Type Type

getFreshInt :: InferState Int
getFreshInt = do n <- get
                 put (n + 1)
                 return n

getFreshTVar :: InferState Type
getFreshTVar = do x <- getFreshInt
                  return (TVar x)

infer :: Env -> Expr -> InferState (Type, ConstraintSet)
infer g (CInt _) = return (TInt, Set.empty)
infer g (CBool _) = return (TBool, Set.empty)
infer g (Var x) = case Map.lookup x g of
                    Just t -> return (t, Set.empty)
                    _      -> return (TError, Set.insert CError Set.empty)                     
infer g (Abs x e) = do y <- getFreshTVar
                       (t, c) <- infer (Map.insert x y g) e
                       return (TArr y t, c)
infer g (Plus e1 e2) = do (t1, c1) <- infer g e1
                          (t2, c2) <- infer g e2
                          -- C1 ∪ C2 ∪ {T1 = Int, T2 = Int}
                          return (TInt, Set.insert (CEq t2 TInt) (Set.insert (CEq t1 TInt) (Set.union c1 c2)))
infer g (Minus e1 e2) = do (t1, c1) <- infer g e1
                           (t2, c2) <- infer g e2
                           --  C1 ∪ C2 ∪ {T1 = Int, T2 = Int}
                           return (TInt, Set.insert (CEq t2 TInt) (Set.insert (CEq t1 TInt) (Set.union c1 c2)))
infer g (Equal e1 e2) = do (t1, c1) <- infer g e1
                           (t2, c2) <- infer g e2
                           --  C = C1 ∪ C2 ∪ {T1 = T2}
                           return (TBool, Set.insert (CEq t1 t2) (Set.union c1 c2))
infer g (ITE e1 e2 e3) = do (t1, c1) <- infer g e1
                            (t2, c2) <- infer g e2
                            (t3, c3) <- infer g e3
                            -- C1 ∪ C2 ∪ C3 ∪ {T1 = Bool, T2 = T3}
                            return (t2, Set.insert (CEq t2 t3) (Set.insert (CEq t1 TBool) (Set.union c3 (Set.union c1 c2))))
infer g (App e1 e2) = do x1 <- getFreshTVar
                         x2 <- getFreshTVar
                         (t1, c1) <- infer g e1
                         (t2, c2) <- infer g e2
                         --  C = C1 ∪ C2 ∪ {T1 = X1 → X2, T2 = X1}
                         return (x2, Set.insert (CEq t2 x1) (Set.insert (CEq t1 (TArr x1 x2) ) (Set.union c1 c2)))
infer g (LetIn x e1 e2) = do y <- getFreshTVar
                             (t1, c1) <- infer (Map.insert x y g) e1
                             (t2, c2) <- infer (Map.insert x y g) e2
                             --  C = C1 ∪ C2 ∪ {X = T1}
                             return (t2, Set.union (Set.singleton (CEq y t1)) (Set.union c1 c2))

inferExpr :: Expr -> (Type, ConstraintSet)
inferExpr e = evalState (infer Map.empty e) 1

toCstrList :: ConstraintSet -> ConstraintList
toCstrList c = Set.toList c 

applySub :: Substitution -> Type -> Type
applySub sub (TInt) = TInt 
applySub sub (TBool) = TBool
applySub sub (TError) = TError
applySub sub (TVar x) = case Map.lookup (TVar x) sub of
                          Just t -> t
                          _      -> (TVar x)  
applySub sub (TArr t1 t2) = TArr (applySub sub t1) (applySub sub t2)

applySubToCstrList :: Substitution -> ConstraintList -> ConstraintList
applySubToCstrList sub [] = []
applySubToCstrList sub (head : tail) = case head of
                                        CEq t1 t2 -> CEq (applySub sub t1) (applySub sub t2) : applySubToCstrList sub tail
                                        CError    -> applySubToCstrList sub tail

composeSub :: Substitution -> Substitution -> Substitution
-- union (X ↦ Tσ1 for each (X ↦ T) ∈ σ2) (X ↦ T for each (X ↦ T) ∈ σ with X ∉ dom(σ2))
composeSub sub1 sub2 = Map.union (Map.map (applySub sub1) sub2) (Map.difference sub1 sub2)

tvars :: Type -> Set.Set Type
tvars (TInt) = Set.empty
tvars (TBool) = Set.empty
tvars (TError) = Set.empty
tvars (TVar var) = Set.singleton (TVar var)
tvars (TArr var1 var2) = Set.union (tvars var1) (tvars var2)

unify :: ConstraintList -> Maybe Substitution
unify [] =  Just Map.empty
unify (head : tail) = case head of
                       CEq x y -> if x == y 
                                    then unify tail 
                                  else case head of
                                        CEq (TVar x) t -> if Set.notMember (TVar x) (Set.insert t Set.empty) then
                                                            case (unify (applySubToCstrList (Map.insert (TVar x) t Map.empty) tail)) of
                                                              Just sub -> Just (composeSub sub (Map.insert (TVar x) t Map.empty))
                                                              _        -> Nothing
                                                          else Nothing
                                        CEq s (TVar x) -> if Set.notMember (TVar x) (Set.insert s Set.empty) then
                                                            case (unify (applySubToCstrList (Map.insert (TVar x) s Map.empty) tail)) of
                                                              Just sub -> Just (composeSub sub (Map.insert (TVar x) s Map.empty))
                                                              _        -> Nothing
                                                          else Nothing
                                        CEq (TArr s1 s2) (TArr t1 t2) -> unify (tail ++ [CEq s1 t1, CEq s2 t2])
                                        _ -> Nothing
                       _ -> Nothing

typing :: Expr -> Maybe Type
typing e = case evalState (infer Map.empty e) 1 of 
            (t, c) -> case unify (toCstrList c) of 
                        Just sub -> Just (applySub sub t)
                        _        -> Nothing

type RelabelState a = State (Map.Map Int Int) a
relabel :: Type -> Type
relabel t = evalState (go t) Map.empty
  where
    go :: Type -> RelabelState Type
    go TInt = return TInt
    go TBool = return TBool
    go TError = return TError
    go (TVar x) = do m <- get
                     case Map.lookup x m of
                      Just v -> return (TVar v)
                      Nothing -> do let n = 1 + Map.size m
                                    put (Map.insert x n m)
                                    return (TVar n)
    go (TArr t1 t2) = do t1' <- go t1
                         t2' <- go t2
                         return (TArr t1' t2')

typeInfer :: Expr -> String
typeInfer e = case (typing e) of
                Just t -> show (relabel t)
                _      -> "Type Error"

-- helper function
readExpr :: String -> Expr
readExpr e = read e :: Expr

main :: IO ()
main = do
  args <- getArgs
  handle <- openFile (args!!0) ReadMode
  contents <- hGetContents handle
  let ls = lines contents
  mapM (\str -> putStrLn (typeInfer (readExpr str))) ls
  hClose handle