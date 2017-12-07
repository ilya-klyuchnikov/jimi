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
  FreeVars (List CaseAlt) where
   exFreeVars [] = []
   exFreeVars ((Alt tc tcas dcas res)::es) = (exFreeVars res) ++ (exFreeVars es)

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

  SubstC (List CaseAlt) where
    applySSubst ssubst [] = []
    applySSubst ssubst ((Alt tc tcas dcas res) :: as) = (Alt tc tcas dcas (applySSubst ssubst res)) :: (applySSubst ssubst as)


applySubToLeftMost : Subst -> Expr -> Expr
applySubToLeftMost sub expr = case expr of
  (AppExpr ex1 ex2) => AppExpr (applySubToLeftMost sub ex1) ex2
  _                 => applySubst sub expr


---------------------------------------------------------------------------------
-- Equality modulo alpha conversion
---------------------------------------------------------------------------------

equal : Expr -> Expr -> Bool
equal (AppExpr ex1l ex1r)
      (AppExpr ex2l ex2r)                     = equal ex1l ex2l && equal ex1r ex2r

equal (LamExpr tv1@(TVar (Var v1) exv1) ex1)
      (LamExpr tv2@(TVar (Var v2) exv2) ex2)  = case (v1==v2) of
                                                True   => equal ex1 ex2
                                                False  => equal ex1 $ applySubst [Sub tv2 (VarExpr tv1)] ex2
equal (LamExpr tv1@(TVar Anonymous exv1) ex1)
      (LamExpr tv2@(TVar (Var v2) exv2) ex2)      = equal ex1 ex2
equal (LamExpr tv1@(TVar (Var v1) exv1) ex1)
      (LamExpr tv2@(TVar Anonymous exv2) ex2)     = equal ex1 ex2
equal (LamExpr tv1@(TVar Anonymous exv1) ex1)
      (LamExpr tv2@(TVar Anonymous exv2) ex2)     = equal ex1 ex2

equal (PiExpr tv1@(TVar (Var v1) exv1) ex1)
      (PiExpr tv2@(TVar (Var v2) exv2) ex2)  = case (v1==v2) of
                                                True   => equal ex1 ex2
                                                False  => equal ex1 $ applySubst [Sub tv2 (VarExpr tv1)] ex2
equal (PiExpr tv1@(TVar Anonymous exv1) ex1)
      (PiExpr tv2@(TVar (Var v2) exv2) ex2)      = equal ex1 ex2
equal (PiExpr tv1@(TVar (Var v1) exv1) ex1)
      (PiExpr tv2@(TVar Anonymous exv2) ex2)     = equal ex1 ex2
equal (PiExpr tv1@(TVar Anonymous exv1) ex1)
      (PiExpr tv2@(TVar Anonymous exv2) ex2)     = equal ex1 ex2

equal (VarExpr tv1@(TVar var1 ex1))
      (VarExpr tv2@(TVar var2 ex2))           = var1==var2
equal (SortExpr s1) (SortExpr s2)             = s1 == s2
equal Unknown Unknown                         = True
equal (LitExpr l1) (LitExpr l2)               = l1 == l2
equal _ _                                     = False

---------------------------------------------------------------------------------
-- Strong Substitions
---------------------------------------------------------------------------------
-- strong substitution is slower than weak substitution, but prevents
-- capturing of variables by means of alpha conversion.
-- caution: very naive and slow implemenation!!!

freshFreeVar : List Variable -> Variable
freshFreeVar vs = Var $ ("v" ++ (show (maxInd vs))) where
  maxInd : List Variable -> Int
  maxInd [] = 1
  maxInd (Anonymous :: vs) = maxInd vs
  maxInd ((Var s) :: vs) = let mayBeInt = (substr 1 (length s) s)
                               thisInd = cast {to = Int} mayBeInt
                           in max thisInd (maxInd vs)

interface StrongSubstC t where
  applySStrongSubst  : SSubst -> t -> t
  applyStrongSubst   : Subst  -> t -> t
  -- default
  applyStrongSubst subst expr  = foldr applySStrongSubst expr subst

mutual
  StrongSubstC Expr where
   applySStrongSubst ssubst@(Sub (TVar vars _) exprs) expr = case expr of
    AppExpr exa exb                                 => AppExpr (applySStrongSubst ssubst exa) (applySStrongSubst ssubst exb)
    LamExpr tv ex                                   => lamSStrongSubst ssubst tv ex
    PiExpr  tv ex                                   => piSStrongSubst ssubst tv ex
    VarExpr tvv@(TVar var expr1)                    => if (var==vars) then exprs else VarExpr (TVar var (applySStrongSubst ssubst expr1))
    CaseExpr expr1 alts t                           => CaseExpr (applySStrongSubst ssubst expr1) (applySStrongSubst ssubst alts) (applySStrongSubst ssubst t)
    exrest                                          => exrest

  StrongSubstC CaseAlt where
    applySStrongSubst ssubst (Alt tc tcas dcas res) = Alt tc tcas dcas (applySStrongSubst ssubst res)

  StrongSubstC (List CaseAlt) where
    applySStrongSubst ssubst [] = []
    applySStrongSubst ssubst (alt :: alts) = (applySStrongSubst ssubst alt) :: (applySStrongSubst ssubst alts)

  lamSStrongSubst : SSubst -> TVariable -> Expr -> Expr
  lamSStrongSubst ssubst@(Sub (TVar vars _) exprs) tv@(TVar var expr1) expr2 =
    if var==vars
      then LamExpr (TVar var (applySStrongSubst ssubst expr1)) expr2
    else if not $ vars `elem` freeVarsExpr2
      then LamExpr (TVar var (applySStrongSubst ssubst expr1)) expr2
    else if not $ var  `elem` freeVarsExprs
      then LamExpr (TVar var (applySStrongSubst ssubst expr1)) (applySStrongSubst ssubst expr2)
    else assert_total $ lamSStrongSubst ssubst freshTV ((applySStrongSubst (Sub tv (VarExpr freshTV))) expr2)
   where
    freeVarsExprs : List Variable
    freeVarsExprs = (exFreeVars exprs)
    freeVarsExpr2 : List Variable
    freeVarsExpr2 = (exFreeVars expr2)
    freeVars      : List Variable
    freeVars      = freeVarsExprs ++ freeVarsExpr2
    freshTV       : TVariable
    freshTV       = (TVar (freshFreeVar freeVars) expr1)

  piSStrongSubst : SSubst -> TVariable -> Expr -> Expr
  piSStrongSubst ssubst@(Sub (TVar vars _) exprs) tv@(TVar var expr1) expr2 =
    if var==vars
      then PiExpr (TVar var (applySStrongSubst ssubst expr1)) expr2
    else if not $ vars `elem` freeVarsExpr2
      then PiExpr (TVar var (applySStrongSubst ssubst expr1)) expr2
    else if not $ var  `elem` freeVarsExprs
      then PiExpr (TVar var (applySStrongSubst ssubst expr1)) (applySStrongSubst ssubst expr2)
    else assert_total $ piSStrongSubst ssubst freshTV ((applySStrongSubst (Sub tv (VarExpr freshTV))) expr2)
   where
    freeVarsExprs : List Variable
    freeVarsExprs = (exFreeVars exprs)
    freeVarsExpr2 : List Variable
    freeVarsExpr2 = (exFreeVars expr2)
    freeVars      : List Variable
    freeVars      = freeVarsExprs ++ freeVarsExpr2
    freshTV       : TVariable
    freshTV       = (TVar (freshFreeVar freeVars) expr1)
