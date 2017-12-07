module TermSupport

import AST

%default total
%access public export

data DeltaRule  = MkDeltaRule TVariable Expr

DeltaRules : Type
DeltaRules = List DeltaRule

mergeDeltaRules : DeltaRules -> DeltaRules -> DeltaRules
mergeDeltaRules r1 r2 = r1 ++ r2

--------------------------------------------------------------------------------
-- Investigating the Redex Structure
--------------------------------------------------------------------------------

data RedexInf = NoRedex
              | BetaRedex
              | CaseRedex
              | DeltaRedex DeltaRule

lookup'' : TVariable -> DeltaRules -> Maybe DeltaRule
lookup'' tv@(TVar (Var v) _) (r@(MkDeltaRule (TVar (Var v') _) _)::rs) =
 if (v==v') then Just r else lookup'' tv rs
lookup'' _ _ = Nothing


redex : DeltaRules -> Expr -> RedexInf
redex deltaRules expr = case expr of
 AppExpr (LamExpr _ _) _  => BetaRedex
 CaseExpr _ _ _           => CaseRedex
 VarExpr tv               => case lookup'' tv deltaRules of
                              Just deltarule  => DeltaRedex deltarule
                              Nothing         => NoRedex
 _                        => NoRedex

isSomeRedex : RedexInf -> Bool
isSomeRedex NoRedex = False
isSomeRedex _       = True

isNoRedex : RedexInf -> Bool
isNoRedex NoRedex = True
isNoRedex _       = False

--------------------------------------------------------------------------------
-- Extracting Sub Expressions
--------------------------------------------------------------------------------
leftMost : Expr -> Expr
leftMost expr = case expr of
 (AppExpr ex1 ex2) => leftMost ex1
 _                 => expr

leftMostApp : Expr -> Expr
leftMostApp expr = case expr of
 (AppExpr ex1 ex2) => case ex1 of
                       (AppExpr exa exb) => leftMostApp ex1
                       _                 => expr
 _                 => idris_crash "leftMostApp"

--------------------------------------------------------------------------------
-- Investigating the Term Structure
--------------------------------------------------------------------------------

isApp : Expr -> Bool
isApp expr = case expr of
 (AppExpr _ _) => True
 _             =>  False

isLam : Expr -> Bool
isLam expr = case expr of
 LamExpr _ _   => True
 _             => False


isPi : Expr -> Bool
isPi expr = case expr of
 PiExpr _ _ => True
 _          => False

isVar : Expr -> Bool
isVar expr = case expr of
 VarExpr _      => True
 _              => False

isSort : Expr -> Bool
isSort expr = case expr of
 SortExpr _     => True
 _              => False

hnf : DeltaRules -> Expr -> Bool
hnf deltaRules expr = case expr of
  LamExpr tv ex1  => hnf deltaRules ex1
  AppExpr _  _    => not $ or (map (\ex => isSomeRedex (redex deltaRules ex)) [leftMostApp expr,leftMost expr])
  _               => isNoRedex (redex deltaRules expr)

whnf : DeltaRules -> Expr -> Bool
whnf deltaRules expr = case expr of
  LamExpr _  _    => True
  AppExpr _  _    => not $ or (map (\ex => isSomeRedex (redex deltaRules ex)) [leftMostApp expr, leftMost expr])
  _               => isNoRedex (redex deltaRules expr)

---------------------------------------------------------------------------------
-- Free Variables
---------------------------------------------------------------------------------
interface FreeVars t where
  exFreeVars : t -> List Variable

mutual
  FreeVars (List Alt) where
   exFreeVars [] = []
   exFreeVars ((MKAlt tc tcas dcas res)::es) = (exFreeVars res) ++ (exFreeVars es)

  FreeVars Expr where
   exFreeVars expr = case expr of
    AppExpr exa exb                                 => exFreeVars exa ++ exFreeVars exb
    LamExpr tv@(TVar var expr1) expr2               => filter (/=var) $ exFreeVars expr1 ++ (exFreeVars expr2)
    PiExpr  tv@(TVar var expr1) expr2               => filter (/=var) $ exFreeVars expr1 ++ (exFreeVars expr2)
    VarExpr tvv@(TVar var expr1)                    => [var] ++ (exFreeVars expr1)
    CaseExpr expr1 alts t                           => exFreeVars expr1 ++ exFreeVars alts ++ exFreeVars t
    LitExpr _                                       => []
    SortExpr _                                      => []
    Unknown                                         => []

---------------------------------------------------------------------------------
-- (Weak) Substitutions
---------------------------------------------------------------------------------

data SSubst = Sub TVariable Expr -- singleton substitution

Subst : Type
Subst = List SSubst

interface SubstC t where
  applySSubst  : SSubst -> t -> t
  applySubst   : Subst  -> t -> t
  -- default
  applySubst subst expr  = foldr applySSubst expr subst

mutual

  SubstC Expr where
   applySSubst ssubst@(Sub (TVar vars _) exprs) expr = case expr of
    AppExpr exa exb                                 => AppExpr (applySSubst ssubst exa) (applySSubst ssubst exb)
    LamExpr tv@(TVar var expr1) expr2               => if (var==vars)
                                                        then LamExpr tv expr2
                                                        else LamExpr (TVar var (applySSubst ssubst expr1)) (applySSubst ssubst expr2)
    PiExpr  tv@(TVar var expr1) expr2               => if (var==vars)
                                                        then PiExpr  tv expr2
                                                        else PiExpr  (TVar var (applySSubst ssubst expr1)) (applySSubst ssubst expr2)
    VarExpr tvv@(TVar var expr1)                    => if (var==vars)
                                                        then exprs
                                                        else VarExpr (TVar var (applySSubst ssubst expr1))
    CaseExpr expr1 alts t                           => CaseExpr (applySSubst ssubst expr1) (applySSubst ssubst alts) (applySSubst ssubst t)
    exrest                                          => exrest

  SubstC (List Alt) where
    applySSubst ssubst [] = []
    applySSubst ssubst ((MKAlt tc tcas dcas res) :: as) = (MKAlt tc tcas dcas (applySSubst ssubst res)) :: (applySSubst ssubst as)


applySubToLeftMost : Subst -> Expr -> Expr
applySubToLeftMost sub expr = case expr of
  (AppExpr ex1 ex2) => AppExpr (applySubToLeftMost sub ex1) ex2
  _                 => applySubst sub expr


---------------------------------------------------------------------------------
-- Strong Substitions
---------------------------------------------------------------------------------
-- strong substitution is slower than weak substitution, but prevents
-- capturing of variables by means of alpha conversion.
-- caution: very naive and slow implemenation!!!
