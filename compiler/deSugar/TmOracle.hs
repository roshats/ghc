
{-
  Author: George Karachalias <george.karachalias@cs.kuleuven.be>
-}

{-# OPTIONS_GHC -Wwarn #-}   -- unused variables

{-# LANGUAGE CPP #-}

module TmOracle
( PmExpr(..), PmLit(..), PmVarEnv, ComplexEq, PmNegLitCt
, hsExprToPmExpr
, lhsExprToPmExpr
, isNotPmExprOther
, pmLitType
, tmOracle
, notForced
, flattenPmVarEnv
, falsePmExpr
, getValuePmExpr
, filterComplex
, runPmPprM
, pprPmExprWithParens
) where

#include "HsVersions.h"

import Type
import TcHsSyn
import HsSyn
import Id
import DataCon
import TysWiredIn
import Outputable
import Util
import MonadUtils
import Control.Arrow (first)
import SrcLoc
import BasicTypes (boxityNormalTupleSort)
import FastString (sLit)

import VarSet
import Data.Maybe (mapMaybe)
import Data.List (foldl', groupBy, sortBy, nub)
import Control.Monad.Trans.State.Lazy
import Control.Monad.Trans.Except
import Control.Monad.Trans.Class (lift)
import qualified Data.Map as Map

{-
%************************************************************************
%*                                                                      *
\subsection{The term equality oracle}
%*                                                                      *
%************************************************************************

-- NOTE [Term oracle strategy]

Because of the incremental nature of the algorithm, initially all constraints
are shallow and most of them are simple equalities between variables. In
general, even if we start only with equalities of the form (x ~ e), the oracle
distinguishes between equalities of 3 different forms:

  * Variable equalities (VE) of the form (x ~ y)
  * Simple   equalities (SE) of the form (x ~ e)
  * Complex  equalities (CE) of the form (e ~ e')

The overall strategy works in 2 phases:

A. Preparation Phase
====================
1) Partition initial set into VE and 'actual simples' SE (partitionSimple).
2) Solve VE (solveVarEqs) and apply the resulting substitution in SE.
3) Repeatedly apply [x |-> e] to SE, as long as a simple equality (x ~ e)
   exists in it (eliminateSimples). The result is a set of 'actual' complex
   equalities CE.

Steps (1),(2),(3) are all performed by `prepComplexEq' on CE, which is the
most general form of equality.

B. Solving Phase
================
1) Try to simplify the constraints by means of flattening, evaluation of
   expressions etc. (simplifyComplexEqs).
2) If some simplification happens, prepare the constraints (prepComplexEq) and
   repeat the Solving Phase.

-}

-- | Lifted version of (HsExpr Id)
data PmExpr = PmExprVar   Id
            | PmExprCon   DataCon [PmExpr]
            | PmExprLit   PmLit
            | PmExprEq    PmExpr PmExpr  -- Syntactic equality
            | PmExprOther (HsExpr Id)    -- NOTE [PmExprOther in PmExpr]

data PmLit = PmSLit HsLit                                    -- simple
           | PmOLit Bool {- is it negated? -} (HsOverLit Id) -- overloaded

instance Eq PmLit where
  PmSLit    l1 == PmSLit l2    = l1 == l2
  PmOLit b1 l1 == PmOLit b2 l2 = b1 == b2 && l1 == l2
  _ == _ = False

isNotPmExprOther :: PmExpr -> Bool
isNotPmExprOther (PmExprOther _) = False
isNotPmExprOther _expr           = True

isNegatedPmLit :: PmLit -> Bool
isNegatedPmLit (PmOLit b _) = b
isNegatedPmLit _other_lit   = False

pmLitType :: PmLit -> Type
pmLitType (PmSLit   lit) = hsLitType   lit
pmLitType (PmOLit _ lit) = overLitType lit

isConsDataCon :: DataCon -> Bool
isConsDataCon con = consDataCon == con

isNilPmExpr :: PmExpr -> Bool
isNilPmExpr (PmExprCon c _) = c == nilDataCon
isNilPmExpr _other_expr     = False

-- ----------------------------------------------------------------------------
-- | Oracle Types

-- | All different kinds of term equalities.
type VarEq     = (Id, Id)
type SimpleEq  = (Id, PmExpr) -- We always use this orientation
type ComplexEq = (PmExpr, PmExpr)

-- | The oracle will try and solve the wanted term constraints. If there is no
-- problem we get back a list of residual constraints. There are 2 types of
-- falures:
--   * Just eq: The set of constraints is non-satisfiable. The eq is evidence
--     (one of the possibly many) of non-satisfiability.
--   * Nothing: The constraints gave rise to a (well-typed) constraint of the
--     form (K ps ~ lit), which actually is equivalent to (K ps ~ from lit),
--     where `from' is the respective overloaded function (fromInteger, etc.)
--     By default we do not unfold functions (not currently, that it) so the
--     oracle gives up (See trac #322).
type Failure = ComplexEq

-- | The oracle environment. As the solver processess the constraints, a
-- substitution theta is generated. Since at every step the algorithm completely
-- eliminates a variable, we end up with a DAG. If there were loops, the
-- algorithm would also loop (we do not inspect function calls that may be
-- recursive so there is not termination problem at the moment).
type PmVarEnv = Map.Map Id PmExpr

type TmOracleEnv = ([ComplexEq], PmVarEnv) -- The first is the things we cannot solve (HsExpr, overloading rubbish, etc.)

-- | The oracle monad.
type TmOracleM a = StateT TmOracleEnv (Except Failure) a -- keep eqs (x~HsExpr) in the environment. We wont do anything with them

-- ----------------------------------------------------------------------------
-- | Oracle utils

-- | Monad stuff
runTmOracleM :: TmOracleM a -> Either Failure (a, TmOracleEnv)
runTmOracleM m = runExcept (runStateT m ([], Map.empty))

liftTmOracleM :: (PmVarEnv -> (res, PmVarEnv)) -> TmOracleM res
liftTmOracleM f = do
  (other_eqs, env) <- get
  let (res, env') = f env
  put (other_eqs, env')
  return res

addUnhandledEqs :: [ComplexEq] -> TmOracleM ()
addUnhandledEqs eqs = modify (first (eqs++))

-- | Not actually a ComplexEq, we just wrap it with a PmExprVar
toComplex :: SimpleEq -> ComplexEq
toComplex = first PmExprVar

-- Extend the substitution
addSubst :: Id -> PmExpr -> PmVarEnv -> PmVarEnv
addSubst x e env = case Map.lookup x env of
  Nothing -> Map.insert x e env
  Just e' -> pprPanic "Check.addSubst:" (ppr x $$ ppr e $$ ppr e') -- just for sanity check

-- ----------------------------------------------------------------------------

-- | Split a set of simple equalities (of the form x ~ expr) into equalities
-- between variables only (x ~ y) and the rest (x ~ expr, where expr not a var)
-- Also, return the equalities of the form (x ~ e), where e is an HsExpr (we cannot handle it)
partitionSimple :: [SimpleEq] -> ([VarEq], [SimpleEq], [SimpleEq])
partitionSimple in_cs = foldr select ([],[],[]) in_cs
  where
    select eq@(x,e) ~(var_eqs, other_eqs, res_eqs)
      | PmExprVar y   <- e = ((x,y):var_eqs,    other_eqs,    res_eqs)
      | PmExprOther _ <- e = (      var_eqs,    other_eqs, eq:res_eqs)
      | otherwise          = (      var_eqs, eq:other_eqs,    res_eqs)

partitionSimpleM :: [SimpleEq] -> TmOracleM ([VarEq], [SimpleEq])
partitionSimpleM in_cs = addUnhandledEqs (map toComplex res_eqs) >> return (var_eqs, other_eqs)
  where (var_eqs, other_eqs, res_eqs) = partitionSimple in_cs

-- | Split a set of complex equalities into into the 3 categories
-- Also, return the equalities of the form (x ~ e), where e is an HsExpr (we cannot handle it)
partitionComplex :: [ComplexEq] -> ([VarEq], [SimpleEq], [ComplexEq], [SimpleEq])
partitionComplex in_cs = foldr select ([],[],[],[]) in_cs
  where
    select eq@(e1,e2) ~(var_eqs, simpl_eqs, other_eqs, res_eqs)
      | PmExprVar x <- e1 = selectSimple x e2 (var_eqs, simpl_eqs, other_eqs, res_eqs)
      | PmExprVar y <- e2 = selectSimple y e1 (var_eqs, simpl_eqs, other_eqs, res_eqs)
      | otherwise         = (var_eqs, simpl_eqs, eq:other_eqs, res_eqs)

    selectSimple x e ~(var_eqs, simpl_eqs, other_eqs, res_eqs)
      | PmExprVar y   <- e = ((x,y):var_eqs,       simpl_eqs, other_eqs,       res_eqs)
      | PmExprOther _ <- e = (      var_eqs,       simpl_eqs, other_eqs, (x,e):res_eqs)
      | otherwise          = (      var_eqs, (x,e):simpl_eqs, other_eqs,       res_eqs)

partitionComplexM :: [ComplexEq] -> TmOracleM ([VarEq], [SimpleEq], [ComplexEq])
partitionComplexM in_cs = addUnhandledEqs (map toComplex res_eqs) >> return (var_eqs, simpl_eqs, other_eqs)
  where (var_eqs, simpl_eqs, other_eqs, res_eqs) = partitionComplex in_cs

-- ----------------------------------------------------------------------------

-- Non-satisfiable set of constraints
mismatch :: ComplexEq -> TmOracleM a
mismatch eq = lift (throwE eq)

-- Expressions `True' and `False'
truePmExpr :: PmExpr
truePmExpr = PmExprCon trueDataCon []

falsePmExpr :: PmExpr
falsePmExpr = PmExprCon falseDataCon []

-- Check if a PmExpression is equal to term `True' (syntactically).
isTruePmExpr :: PmExpr -> Bool
isTruePmExpr (PmExprCon c []) = c == trueDataCon
isTruePmExpr _other_expr      = False

-- Check if a PmExpression is equal to term `False' (syntactically).
isFalsePmExpr :: PmExpr -> Bool
isFalsePmExpr (PmExprCon c []) = c == falseDataCon
isFalsePmExpr _other_expr      = False

isPmExprEq :: PmExpr -> Maybe (PmExpr, PmExpr)
isPmExprEq (PmExprEq e1 e2) = Just (e1,e2)
isPmExprEq _other_expr      = Nothing

-- ----------------------------------------------------------------------------
-- | Substitution for PmExpr

substPmExpr :: Id -> PmExpr -> PmExpr -> PmExpr
substPmExpr x e1 e =
  case e of
    PmExprVar z | x == z    -> e1
                | otherwise -> e
    PmExprCon c ps -> PmExprCon c (map (substPmExpr x e1) ps)
    PmExprEq ex ey -> PmExprEq (substPmExpr x e1 ex) (substPmExpr x e1 ey)
    _other_expr    -> e -- The rest are terminals -- we silently ignore
                        -- PmExprOther. See NOTE [PmExprOther in PmExpr]

idSubstPmExpr :: (Id -> Id) -> PmExpr -> PmExpr
idSubstPmExpr fn e =
  case e of
    PmExprVar z    -> PmExprVar (fn z)
    PmExprCon c es -> PmExprCon c (map (idSubstPmExpr fn) es)
    PmExprEq e1 e2 -> PmExprEq (idSubstPmExpr fn e1) (idSubstPmExpr fn e2)
    _other_expr    -> e -- The rest are terminals -- we silently ignore
                        -- PmExprOther. See NOTE [PmExprOther in PmExpr]

-- ----------------------------------------------------------------------------
-- | Substitution in term equalities

idSubstVarEq :: (Id -> Id) -> VarEq -> VarEq
idSubstVarEq fn (x, y) = (fn x, fn y)

idSubstSimpleEq :: (Id -> Id) -> SimpleEq -> SimpleEq
idSubstSimpleEq fn (x,e) = (fn x, idSubstPmExpr fn e)

idSubstComplexEq :: (Id -> Id) -> ComplexEq -> ComplexEq
idSubstComplexEq fn (e1,e2) = (idSubstPmExpr fn e1, idSubstPmExpr fn e2)

substComplexEq :: Id -> PmExpr -> ComplexEq -> ComplexEq
substComplexEq x e (e1, e2) = (substPmExpr x e e1, substPmExpr x e e2)

-- Faster than calling `substSimpleEq' and splitting them afterwards
substSimpleEqs :: Id -> PmExpr -> [SimpleEq] -> ([SimpleEq], [ComplexEq])
substSimpleEqs _ _ [] = ([],[])
substSimpleEqs x e ((y,e1):rest)
  | x == y    = (simple_eqs, (e, e2):complex_eqs)
  | otherwise = ((y, e2):simple_eqs, complex_eqs)
  where (simple_eqs, complex_eqs) = substSimpleEqs x e rest
        e2 = substPmExpr x e e1

-- ----------------------------------------------------------------------------
-- | Solving equalities between variables

-- | A set of equalities between variables is always satisfiable.
solveVarEqs :: PmVarEnv -> [VarEq] -> (Id -> Id, PmVarEnv)
solveVarEqs env eqs = foldl' combine (id, env) eqs
  where
    combine (f, e) = first (.f) . solveVarEq e . idSubstVarEq f

solveVarEq :: PmVarEnv -> VarEq -> (Id -> Id, PmVarEnv)
solveVarEq env (x,y)
  | x == y    = (id, env)
  | otherwise = (subst, addSubst y (PmExprVar x) env)
  where subst = \z -> if z == y then x else z -- (x,y) -> [y |-> x]

-- Monadic version
solveVarEqsM :: [VarEq] -> TmOracleM (Id -> Id)
solveVarEqsM var_eqs = liftTmOracleM (\env -> solveVarEqs env var_eqs)

-- ----------------------------------------------------------------------------
-- | Solving simple equalities

eliminateSimples :: PmVarEnv -> [SimpleEq] -> [ComplexEq] -> ([ComplexEq], PmVarEnv)
eliminateSimples env [] complex_eqs = (complex_eqs, env)
eliminateSimples env ((x,e):eqs) complex_eqs
  = eliminateSimples env' simple_eqs (complex_eqs1 ++ complex_eqs2)
  where
    env' = addSubst x e env
    (simple_eqs, complex_eqs1) = substSimpleEqs x e eqs
    complex_eqs2 = map (substComplexEq x e) complex_eqs

-- Monadic version
eliminateSimplesM :: [SimpleEq] -> [ComplexEq] -> TmOracleM [ComplexEq]
eliminateSimplesM simple_eqs complex_eqs
  = liftTmOracleM (\env -> eliminateSimples env simple_eqs complex_eqs)

-- ----------------------------------------------------------------------------
-- | Solving complex equalities (workhorse)

prepComplexEqM :: [ComplexEq] -> TmOracleM [ComplexEq]
prepComplexEqM []  = return []
prepComplexEqM eqs = do
  (var_eqs, simple_eqs', complex_eqs') <- partitionComplexM eqs
  subst <- solveVarEqsM var_eqs
  let simple_eqs  = map (idSubstSimpleEq  subst) simple_eqs'
  let complex_eqs = map (idSubstComplexEq subst) complex_eqs'
  eliminateSimplesM simple_eqs complex_eqs

-- NB: Call only on prepped equalities (e.g. after prepComplexEq)
iterateComplex :: [ComplexEq] -> TmOracleM [ComplexEq]
iterateComplex []  = return []
iterateComplex eqs = do
  (done, eqs') <- simplifyComplexEqs eqs -- did we have any progress? continue
  if done then prepComplexEqM eqs' >>= iterateComplex
          else return eqs'               -- otherwise, return residual

simplifyComplexEqs :: [ComplexEq] -> TmOracleM (Bool, [ComplexEq])
simplifyComplexEqs eqs = do
  (done, new_eqs) <- mapAndUnzipM simplifyComplexEq eqs
  return (or done, concat new_eqs)

simplifyComplexEq :: ComplexEq -> TmOracleM (Bool, [ComplexEq])
simplifyComplexEq eq =
  case eq of
    -- variables
    (PmExprVar x, PmExprVar y)
      | x == y    -> return (True, [])
      | otherwise -> return (False, [eq])
    (PmExprVar _, _) -> return (False, [eq])
    (_, PmExprVar _) -> return (False, [eq])

    -- literals
    (PmExprLit l1, PmExprLit l2)
      | l1 == l2  -> return (True, [])
      | otherwise -> mismatch eq

    -- constructors
    (PmExprCon c1 es1, PmExprCon c2 es2)
      | c1 == c2  -> simplifyComplexEqs (es1 `zip` es2)
      | otherwise -> mismatch eq

    -- See NOTE [Deep equalities]
    (PmExprCon c es, PmExprEq e1 e2) -> handleDeepEq c es e1 e2
    (PmExprEq e1 e2, PmExprCon c es) -> handleDeepEq c es e1 e2

    -- Overloaded error
    (PmExprCon _ _, PmExprLit l)
      | PmOLit {} <- l -> overloaded_syntax
      | otherwise      -> panic "simplifyComplexEq: constructor-literal"
    (PmExprLit l, PmExprCon _ _)
      | PmOLit {} <- l -> overloaded_syntax
      | otherwise      -> panic "simplifyComplexEq: literal-constructor"

    _other_equality -> return (False, [eq]) -- can't simplify :(

  where
    overloaded_syntax = addUnhandledEqs [eq] >> return (True,[])

    handleDeepEq :: DataCon -> [PmExpr] -- constructor and arguments
                 -> PmExpr  -> PmExpr   -- the equality
                 -> TmOracleM (Bool, [ComplexEq])
    handleDeepEq c es e1 e2
      | c == trueDataCon = do
          (_, new) <- simplifyComplexEq (e1,e2)
          return (True, new)
      | otherwise = do
         let pmexpr = certainlyEqual e1 e2
         if isTruePmExpr pmexpr || isFalsePmExpr pmexpr
            then return (True,  [(PmExprCon c es,pmexpr)])
            else return (False, [eq])

certainlyEqual :: PmExpr -> PmExpr -> PmExpr -- NOTE [Deep equalities]
certainlyEqual e1 e2 =
  case (e1, e2) of

    -- Simple cases
    (PmExprVar  x, PmExprVar  y) -> eqVars x y  -- variables
    (PmExprLit l1, PmExprLit l2) -> eqLit l1 l2 -- literals

    -- Constructor case (unfold)
    (PmExprCon c1 es1, PmExprCon c2 es2) -- constructors
      | c1 == c2  -> certainlyEqualMany es1 es2
      | otherwise -> falsePmExpr

    -- Cannot be sure about the rest
    _other_equality -> expr -- Not really expressive, are we?

  where
    expr = PmExprEq e1 e2 -- reconstruct the equality from the arguments

    eqVars :: Id -> Id -> PmExpr
    eqVars x y = if x == y then truePmExpr else expr

    eqLit :: PmLit -> PmLit -> PmExpr
    eqLit l1 l2 = case (l1, l2) of
      (PmSLit {}, PmSLit {})
        | l1 == l2  -> truePmExpr
        | otherwise -> falsePmExpr
      (PmOLit {}, PmOLit {})
        | l1 == l2  -> truePmExpr
        | otherwise -> falsePmExpr
      _overloaded   -> expr

    certainlyEqualMany :: [PmExpr] -> [PmExpr] -> PmExpr
    certainlyEqualMany es1 es2 =
      let args   = zipWith certainlyEqual es1 es2
          result | all isTruePmExpr  args = truePmExpr
                 | any isFalsePmExpr args = falsePmExpr
                 | otherwise              = expr -- inconclusive
      in  result

-- ----------------------------------------------------------------------------
-- | Entry point to the solver

tmOracle :: [SimpleEq] -> Either Failure ([ComplexEq], TmOracleEnv) -- return residual constraints and final mapping
tmOracle simple_eqs = runTmOracleM (solveAll simple_eqs)

solveAll :: [SimpleEq] -> TmOracleM [ComplexEq]
solveAll []  = return []
solveAll eqs = do
  (var_eqs, simple_eqs') <- partitionSimpleM eqs
  subst <- solveVarEqsM var_eqs
  let simple_eqs = map (idSubstSimpleEq subst) simple_eqs'
  complex_eqs <- eliminateSimplesM simple_eqs []
  iterateComplex complex_eqs

-- ----------------------------------------------------------------------------

getValuePmExpr :: PmVarEnv -> PmExpr -> PmExpr
getValuePmExpr env (PmExprVar x)
  | Just e <- Map.lookup x env = getValuePmExpr env e
  | otherwise                  = PmExprVar x
getValuePmExpr env (PmExprCon c es) = PmExprCon c (map (getValuePmExpr env) es)
getValuePmExpr env (PmExprEq e1 e2) = PmExprEq (getValuePmExpr env e1) (getValuePmExpr env e2)
getValuePmExpr _   other_expr       = other_expr

notForced :: Id -> PmVarEnv -> Bool
notForced x env = case getValuePmExpr env (PmExprVar x) of
  PmExprVar _ -> True
  _other_expr -> False

-- Not really efficient, it recomputes stuff
flattenPmVarEnv :: PmVarEnv -> PmVarEnv
flattenPmVarEnv env = Map.map (getValuePmExpr env) env

-- ----------------------------------------------------------------------------

-- NOTE [Representation of substitution]
--
-- Throughout the code we use 2 different ways to represent substitutions:
--   * Substitutions from variables to variables are represented using Haskell
--     functions with type (Id -> Id).
--   * Substitutions from variables to expressions are usually passed explicitly
--     as two arguments (the Id and the PmExpr to substitute it with)
-- By convention, substitutions of the first kind are prefixed by `idSubst'
-- while the latter are prefixed simply by 'subst'.


-- NOTE [PmExprOther in PmExpr]
--
-- Data constructor `PmExprOther' lifts an (HsExpr Id) to a PmExpr. Ideally we
-- would have only (HsExpr Id) but this would be really verbose:
--    The solver is pretty naive and cannot handle many Haskell expressions.
-- Since there is no plan (for the near future) to change the solver there
-- is no need to work with the full HsExpr type (more than 45 constructors).
--
-- Functions `substPmExpr' and `idSubstPmExpr' do not substitute in HsExpr, which
-- could be a problem for a different solver. E.g:
--
-- For the following set of constraints (HsExpr in braces):
--
--   (y ~ x, y ~ z, y ~ True, y ~ False, {not y})
--
-- would be simplified (in one step using `solveVarEqs') to:
--
--   (x ~ True, x ~ False, {not y})
--
-- i.e. y is now free to be unified with anything! This is not a problem now
-- because we never inspect a PmExprOther (They always end up in residual)
-- but a more sophisticated solver may need to do so!


-- NOTE [Deep equalities]
--
-- Solving nested equalities is the most difficult part. The general strategy
-- is the following:
--
--   * Equalities of the form (True ~ (e1 ~ e2)) are transformed to just
--     (e1 ~ e2) and then treated recursively.
--
--   * Equalities of the form (False ~ (e1 ~ e2)) cannot be analyzed unless
--     we know more about the inner equality (e1 ~ e2). That's exactly what
--     `certainlyEqual' tries to do: It takes e1 and e2 and either returns
--     truePmExpr, falsePmExpr or (e1' ~ e2') in case it is uncertain. Note
--     that it is not e but rather e', since it may perform some
--     simplifications deeper.

-- -----------------------------------------------------------------------
-- | Transform source expressions (HsExpr Id) to PmExpr

-- | We lose information but we have to abstract over it
-- to get the results we want. Impossible to play with HsSyn

lhsExprToPmExpr :: LHsExpr Id -> PmExpr
lhsExprToPmExpr (L _ e) = hsExprToPmExpr e

hsExprToPmExpr :: HsExpr Id -> PmExpr

hsExprToPmExpr (HsVar         x) = PmExprVar x
hsExprToPmExpr (HsOverLit  olit) = PmExprLit (PmOLit False olit)
hsExprToPmExpr (HsLit       lit) = PmExprLit (PmSLit lit)

hsExprToPmExpr e@(NegApp _ neg_e)
  | PmExprLit (PmOLit False ol) <- hsExprToPmExpr neg_e = PmExprLit (PmOLit True ol)
  | otherwise                                           = PmExprOther e
hsExprToPmExpr (HsPar   (L _ e)) = hsExprToPmExpr e

hsExprToPmExpr e@(ExplicitTuple ps boxity)
  | all tupArgPresent ps = PmExprCon tuple_con tuple_args
  | otherwise            = PmExprOther e
  where
    tuple_con  = tupleCon (boxityNormalTupleSort boxity) (length ps)
    tuple_args = [ lhsExprToPmExpr e | L _ (Present e) <- ps ]

hsExprToPmExpr e@(ExplicitList _elem_ty mb_ol elems)
  | Nothing <- mb_ol = foldr cons nil (map lhsExprToPmExpr elems)
  | otherwise        = PmExprOther e {- overloaded list: No PmExprApp -}
  where
    cons x xs = PmExprCon consDataCon [x,xs]
    nil       = PmExprCon nilDataCon  []

hsExprToPmExpr (ExplicitPArr _elem_ty elems)
  = PmExprCon (parrFakeCon (length elems)) (map lhsExprToPmExpr elems)

-- Try and handle this case, it will look like a constructor pattern
-- hsExprToPmExpr e@(RecordCon     _ _ _) = PmExprOther e

hsExprToPmExpr (HsTick            _ e) = lhsExprToPmExpr e
hsExprToPmExpr (HsBinTick       _ _ e) = lhsExprToPmExpr e
hsExprToPmExpr (HsTickPragma      _ e) = lhsExprToPmExpr e
hsExprToPmExpr (HsSCC             _ e) = lhsExprToPmExpr e
hsExprToPmExpr (HsCoreAnn         _ e) = lhsExprToPmExpr e
hsExprToPmExpr (ExprWithTySig   e _ _) = lhsExprToPmExpr e
hsExprToPmExpr (ExprWithTySigOut  e _) = lhsExprToPmExpr e

hsExprToPmExpr e = PmExprOther e -- the rest are not handled by the oracle

{-
%************************************************************************
%*                                                                      *
\subsection{Pretty printing}
%*                                                                      *
%************************************************************************
-}


-- -----------------------------------------------------------------------------
-- | Transform residual constraints in appropriate form for pretty printing

type PmNegLitCt = (Id, (SDoc, [PmLit]))

filterComplex :: [ComplexEq] -> [PmNegLitCt]
filterComplex = zipWith rename nameList . map mkGroup
              . groupBy name . sortBy order . mapMaybe isNegLitCs
  where
    order x y = compare (fst x) (fst y)
    name  x y = fst x == fst y
    mkGroup l = (fst (head l), nub $ map snd l)
    rename new (old, lits) = (old, (new, lits))

    isNegLitCs (e1,e2)
      | isFalsePmExpr e1, Just (x,y) <- isPmExprEq e2 = isNegLitCs' x y
      | isFalsePmExpr e2, Just (x,y) <- isPmExprEq e1 = isNegLitCs' x y
      | otherwise = Nothing

    isNegLitCs' (PmExprVar x) (PmExprLit l) = Just (x, l)
    isNegLitCs' (PmExprLit l) (PmExprVar x) = Just (x, l)
    isNegLitCs' _ _             = Nothing

    nameList :: [SDoc]
    nameList = [ ptext (sLit ('t':show u)) | u <- [(0 :: Int)..] ]

-- ----------------------------------------------------------------------------

runPmPprM :: PmPprM a -> [PmNegLitCt] -> (a, [(SDoc,[PmLit])])
runPmPprM m lit_env = (result, mapMaybe is_used lit_env)
  where
    (result, (_lit_env, used)) = runState m (lit_env, emptyVarSet)

    is_used (x,(name, lits))
      | elemVarSet x used = Just (name, lits)
      | otherwise         = Nothing

type PmPprM a = State ([PmNegLitCt], IdSet) a

addUsed :: Id -> PmPprM ()
addUsed x = modify (\(negated, used) -> (negated, extendVarSet used x))

checkNegation :: Id -> PmPprM (Maybe SDoc) -- the the clean name if it is negated
checkNegation x = do
  negated <- gets fst
  return $ case lookup x negated of
    Just (new, _) -> Just new
    Nothing       -> Nothing

-- | Pretty print a pmexpr, but remember to prettify the names of the variables that refer to neg-literals
-- what you cannot say leave it an underscore
pprPmExpr :: PmExpr -> PmPprM SDoc -- the first part of the state is read only. make it a reader? :/
pprPmExpr (PmExprVar x) = do
  mb_name <- checkNegation x
  case mb_name of
    Just name -> addUsed x >> return name
    Nothing   -> return $ if debugIsOn then ppr x
                                       else underscore
pprPmExpr (PmExprCon con args) = pprPmExprCon con args
pprPmExpr (PmExprLit l) = return (ppr l)
pprPmExpr (PmExprEq e1 e2)
  | debugIsOn = do
      e1' <- pprPmExpr e1
      e2' <- pprPmExpr e2
      return $ braces (e1' <+> equals <+> e2')
  | otherwise = return underscore
pprPmExpr (PmExprOther e)
  | debugIsOn = return (ppr e)
  | otherwise = return underscore

needsParens :: PmExpr -> Bool
needsParens (PmExprVar   {}) = False
needsParens (PmExprLit    l) = isNegatedPmLit l
needsParens (PmExprEq    {}) = False -- will become a wildcard
needsParens (PmExprOther {}) = False -- will become a wildcard
needsParens (PmExprCon c es)
  | isTupleDataCon c || isPArrFakeCon c
  || isConsDataCon c || null es = False
  | otherwise                   = True

pprPmExprWithParens :: PmExpr -> PmPprM SDoc
pprPmExprWithParens expr
  | needsParens expr = parens <$> pprPmExpr expr
  | otherwise        =            pprPmExpr expr

pprPmExprCon :: DataCon -> [PmExpr] -> PmPprM SDoc
pprPmExprCon con args
  | isTupleDataCon con = mkTuple <$> mapM pprPmExpr args
  |  isPArrFakeCon con = mkPArr  <$> mapM pprPmExpr args
  |  isConsDataCon con = pretty_list
  | dataConIsInfix con = case args of
      [x, y] -> do x' <- pprPmExprWithParens x
                   y' <- pprPmExprWithParens y
                   return (x' <+> ppr con <+> y')
      list   -> pprPanic "pprPmExprCon:" (ppr list) -- how can it be infix and have more than two arguments?
  | null args = return (ppr con)
  | otherwise = do args' <- mapM pprPmExprWithParens args
                   return (fsep (ppr con : args'))
  where
    mkTuple, mkPArr :: [SDoc] -> SDoc
    mkTuple = parens     . fsep . punctuate comma
    mkPArr  = paBrackets . fsep . punctuate comma

    -- lazily, to be used in the list case only
    pretty_list :: PmPprM SDoc
    pretty_list = case isNilPmExpr (last elements) of
      True  -> brackets . fsep . punctuate comma <$> mapM pprPmExpr (init elements)
      False -> parens   . hcat . punctuate colon <$> mapM pprPmExpr elements

    elements = list_elements args

    list_elements [x,y]
      | PmExprCon c es <- y,  nilDataCon == c = ASSERT (null es) [x,y]
      | PmExprCon c es <- y, consDataCon == c = x : list_elements es
      | otherwise = [x,y]
    list_elements list  = pprPanic "list_elements:" (ppr list)

instance Outputable PmLit where
  ppr (PmSLit     l) = pmPprHsLit l
  ppr (PmOLit neg l) = (if neg then char '-' else empty) <> ppr l

-- not really useful for pmexprs per se
instance Outputable PmExpr where
  ppr e = fst $ runPmPprM (pprPmExpr e) []

