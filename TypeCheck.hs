{-# LANGUAGE FlexibleInstances, OverloadedStrings, BangPatterns #-}

module Language.Nano.TypeCheck where

import Language.Nano.Types
import Language.Nano.Parser

import qualified Data.List as L
import           Text.Printf (printf)  
import           Control.Exception (throw)
import Data.Functor.Classes (eq1)
import Foreign.C (e2BIG)
import Control.Monad (when)

--------------------------------------------------------------------------------
typeOfFile :: FilePath -> IO Type
typeOfFile f = parseFile f >>= typeOfExpr

typeOfString :: String -> IO Type
typeOfString s = typeOfExpr (parseString s)

typeOfExpr :: Expr -> IO Type
typeOfExpr e = do
  let (!st, t) = infer initInferState preludeTypes e
  if (length (stSub st)) < 0 then throw (Error ("count Negative: " ++ show (stCnt st)))
  else return t

--------------------------------------------------------------------------------
-- Warm-up
--------------------------------------------------------------------------------

-- | Things that have free type variables
class HasTVars a where
  freeTVars :: a -> [TVar]

-- | Type variables of a type
instance HasTVars Type where
  freeTVars TInt        = []
  freeTVars TBool       = []
  freeTVars (TVar t)   = [t]
  freeTVars (x :=> y) = L.nub (freeTVars x ++ freeTVars y)
  freeTVars (TList t)   = freeTVars t

-- | Free type variables of a poly-type (remove forall-bound vars)
instance HasTVars Poly where
  freeTVars (Mono s) = freeTVars s
  freeTVars (Forall id s) = filter (/= id) (freeTVars s)

-- | Free type variables of a type environment
instance HasTVars TypeEnv where
  freeTVars gamma   = concat [freeTVars s | (x, s) <- gamma]  
  
-- | Lookup a variable in the type environment  
lookupVarType :: Id -> TypeEnv -> Poly
lookupVarType x ((y, s) : gamma)
  | x == y    = s
  | otherwise = lookupVarType x gamma
lookupVarType x [] = throw (Error ("unbound variable: " ++ x))

-- | Extend the type environment with a new biding
extendTypeEnv :: Id -> Poly -> TypeEnv -> TypeEnv
extendTypeEnv x s gamma = (x,s) : gamma  

-- | Lookup a type variable in a substitution;
--   if not present, return the variable unchanged
lookupTVar :: TVar -> Subst -> Type
lookupTVar a [] = TVar a 
lookupTVar a ((x, y):sub) =
  if a == x then
    y
  else
    (case sub of
       [] -> TVar a
       _ -> lookupTVar a sub)

-- | Remove a type variable from a substitution
removeTVar :: TVar -> Subst -> Subst
removeTVar a sub = filter (\(x, _) -> x /= a) sub
     
-- | Things to which type substitutions can be apply
class Substitutable a where
  apply :: Subst -> a -> a
  
-- | Apply substitution to type
instance Substitutable Type where  
  apply sub t = case t of
    TInt -> TInt
    TBool -> TBool
    x :=> y -> apply sub x :=> apply sub y
    TVar a -> lookupTVar a sub
    TList t' -> TList (apply sub t')

-- | Apply substitution to poly-type
instance Substitutable Poly where 
  apply sub s = case s of
    Mono t -> Mono (apply sub t)
    Forall temp x -> 
      if temp `elem` map fst sub
      then let sub' = filter ((/= temp) . fst) sub in Forall temp (apply sub' x)
      else Forall temp (apply sub x)

-- | Apply substitution to (all poly-types in) another substitution
instance Substitutable Subst where  
  apply sub to = zip keys $ map (apply sub) vals
    where
      (keys, vals) = unzip to
      
-- | Apply substitution to a type environment
instance Substitutable TypeEnv where  
  apply sub gamma = zip keys $ map (apply sub) vals
    where
      (keys, vals) = unzip gamma
      
-- | Extend substitution with a new type assignment
extendSubst :: Subst -> TVar -> Type -> Subst
extendSubst sub a t =
  let
    x = apply sub t
    y = filter (\(x, _) -> x /= a) sub
  in
    (a, x) : y
      
--------------------------------------------------------------------------------
-- Unification
--------------------------------------------------------------------------------
      
-- | State of the type inference algorithm      
data InferState = InferState { 
    stSub :: Subst -- ^ current substitution
  , stCnt :: Int   -- ^ number of fresh type variables generated so far
} deriving (Eq,Show)

-- | Initial state: empty substitution; 0 type variables
initInferState = InferState [] 0

-- | Fresh type variable number n
freshTV n = TVar $ "a" ++ show n      
    
-- | Extend the current substitution of a state with a new type assignment   
extendState :: InferState -> TVar -> Type -> InferState
extendState (InferState sub n) a t = InferState (extendSubst sub a t) n
        
-- | Unify a type variable with a type; 
--   if successful return an updated state, otherwise throw an error
unifyTVar :: InferState -> TVar -> Type -> InferState
unifyTVar st a t 
  | t == TVar a                          = st
  | temp /= TVar a                       = unify st temp t
  | L.elem a (freeTVars t)               = throw(Error("type error: cannot unify " ++ a ++ " and " ++ show t ++ " (occurs check)"))
  | otherwise                            = extendState st a t
    where temp = lookupTVar a (stSub st)

    
-- | Unify two types;
--   if successful return an updated state, otherwise throw an error
unify :: InferState -> Type -> Type -> InferState
unify st t1 t2 = case (t1, t2) of
    (TVar a, t) -> unifyTVar st a t
    (t, TVar a) -> unifyTVar st a t
    (TInt, TInt) -> st
    (TBool, TBool) -> st
    (TList t1, TList t2) -> unify st t1 t2
    (t1 :=> t2, t3 :=> t4) -> 
        let x = unify st t1 t3
        in unify x t2 t4
    _ -> if t1 == t2 
         then st 
         else throw (Error ("type error: cannot unify " ++ show t1 ++ " and " ++ show t2))

--------------------------------------------------------------------------------
-- Type Inference
--------------------------------------------------------------------------------    
  
infer :: InferState -> TypeEnv -> Expr -> (InferState, Type)
infer st _   (EInt _)          = (st, TInt)
infer st _   (EBool _)         = (st, TBool)
infer st gamma (EVar x)        = (st', t') -- implemented in Friday section
  where
    t = lookupVarType x gamma
    (n', t') = instantiate (stCnt st) t
    st' = InferState (stSub st) n'

infer st gamma (ELam x body)   = (st', input2 :=> bodyT) -- implemented in Friday section
  where
    input           = freshTV (stCnt st)                     
    gamma'          = extendTypeEnv x (Mono input) gamma        
    st1             = InferState (stSub st) ((stCnt st) + 1)  
    (st', bodyT)    = infer st1 gamma' body                 
    input2          = apply (stSub st') input

infer st gamma (EApp e1 e2) = (st4, t) -- started implemention in Friday section
  where
    (TVar input)      = freshTV (stCnt st)
    st3               = InferState (stSub st) ((stCnt st)+1) 
    (st1, t')         = infer st3 gamma e1
    (st2, t'')        = infer st1 gamma e2
    bodyT             = (t'' :=> (TVar input))
    st4               = unify st2 t' bodyT
    t                 = lookupTVar input (stSub st4)

infer st gamma (ELet x e1 e2) = (st3, t'') -- started implemention in Friday section
  where
    input = freshTV (stCnt st)
    gamma' = extendTypeEnv x (Mono input) gamma
    st4 = InferState (stSub st) ((stCnt st) + 1)
    (st2, t') = infer st4 gamma' e1
    input' = generalize gamma' t' 
    bodyT = extendTypeEnv x input' gamma
    st5 = unify st2 input t'
    (st3, t'') = infer st5 bodyT e2

infer st gamma (EBin op e1 e2) = infer st gamma asApp
  where
    asApp = EApp (EApp opVar e1) e2
    opVar = EVar (show op)
infer st gamma (EIf c e1 e2) = infer st gamma asApp
  where
    asApp = EApp (EApp (EApp ifVar c) e1) e2
    ifVar = EVar "if"    
infer st gamma ENil = infer st gamma (EVar "[]")

-- | Generalize type variables inside a type
generalize :: TypeEnv -> Type -> Poly
generalize gamma t = foldr Forall (Mono t) freeVars
  where
    freeVars = freeTVars t L.\\ freeTVars gamma
    
-- | Instantiate a polymorphic type into a mono-type with fresh type variables
instantiate :: Int -> Poly -> (Int, Type)
instantiate n (Mono input) = (n, input)
instantiate n (Forall id input) =
    let (n', fresh) = (n + 1, freshTV n)
        sub = extendSubst [] id fresh
    in instantiate n' (apply sub input)
      
-- | Types of built-in operators and functions      
preludeTypes :: TypeEnv
preludeTypes =
  [ ("+",    Mono $ TInt :=> TInt :=> TInt)
  , ("-",    Mono $ TInt :=> TInt :=> TInt)
  , ("*",    Mono $ TInt :=> TInt :=> TInt)
  , ("/",    Mono $ TInt :=> TInt :=> TInt)
  , ("==",   Forall "a" $ Mono $ TVar "a" :=> TVar "a" :=> TBool)
  , ("!=",   Forall "a" $ Mono $ TVar "a" :=> TVar "a" :=> TBool)
  , ("<",    Mono $ TInt :=> TInt :=> TBool)
  , ("<=",   Mono $ TInt :=> TInt :=> TBool)
  , ("&&",   Mono $ TBool :=> TBool :=> TBool)
  , ("||",   Mono $ TBool :=> TBool :=> TBool)
  , ("if",   Forall "a" $ Mono $ TBool :=> TVar "a" :=> TVar "a" :=> TVar "a")
  -- lists: 
  , ("[]",   Forall "a" $ Mono $ TList (TVar "a"))
  , (":",    Forall "a" $ Mono $ TVar "a" :=> TList (TVar "a") :=> TList (TVar "a"))
  , ("head", Forall "a" $ Mono $ TList (TVar "a") :=> TVar "a")
  , ("tail", Forall "a" $ Mono $ TList (TVar "a") :=> TList (TVar "a"))
  ]
