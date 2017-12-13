module Reduce

import AST
import TermSupport

%default total
%access public export

--------------------------------------------------------------------------------
-- Delta Rules
--------------------------------------------------------------------------------

vDecl2DeltaRule : VDeclaration -> DeltaRule
vDecl2DeltaRule (VDecl tv ex)  = MkDeltaRule tv ex

prog2DeltaRules : Program -> DeltaRules
prog2DeltaRules (Prog _ vdecls) = map vDecl2DeltaRule vdecls

--------------------------------------------------------------------------------
-- Reducing Redexes
--------------------------------------------------------------------------------
lookupA' : Expr -> List CaseAlt -> Maybe CaseAlt
lookupA' ex ((a@(Alt  tc@(TVar va _) _ _ _)) :: as) = case ex of
  (VarExpr (TVar v _)) => if v == va  then Just a else lookupA' ex as
  _                    => lookupA' ex as
lookupA' ex []    = Nothing

lookupA : Expr -> List CaseAlt -> Maybe CaseAlt
lookupA ex alts = lookupA' (leftMost ex) alts

reduceBeta : Expr -> Expr
reduceBeta (AppExpr  (LamExpr tv ex1) ex2) = applySubst [(Sub tv ex2)] ex1
reduceBeta e = idris_crash ("reduceBeta: " ++ show e)

reduceDeltaRule : Expr -> DeltaRule -> Expr
reduceDeltaRule _ (MkDeltaRule _ ex2) = ex2

mutual
  reduceRedex : DeltaRules -> RedexInf -> Expr -> Expr
  reduceRedex dr ri ex = case ri of
    BetaRedex      => reduceBeta ex
    CaseRedex      => reduceCase dr ex
    DeltaRedex dr1 => reduceDeltaRule ex dr1
    NoRedex        => idris_crash "NoRedex"

  reduceCase : DeltaRules -> Expr -> Expr
  reduceCase dr ce@(CaseExpr ex alts _) =
    let whnf = reduce_to_whnf dr ex
    in
      case lookupA whnf alts of
        Just (Alt tc tcas dcas res) => applySubToLeftMost [Sub tc (foldr LamExpr res (tcas++dcas))] whnf
        Nothing                     => idris_crash $ "runtime error: missing alternative (" ++ show (leftMost whnf) ++") in case expression!!\n" ++ (show ce)
  reduceCase dr e = idris_crash ("reduceCase " ++ (show e))

  weak : DeltaRules -> Expr -> Maybe Expr
  weak dr ex = let redexinf = (redex dr ex)
                in
                  if isSomeRedex redexinf
                    then let reduced  = (reduceRedex dr redexinf ex)
                      in (weak dr (assert_smaller ex reduced)) <|> (Just reduced)
                  else if isApp  ex
                    then weakApp dr ex
                  else
                    Nothing

  weakApp : DeltaRules -> Expr -> Maybe Expr
  weakApp dr app@(AppExpr ex1 ex2) =
   case (weak dr ex1) of
     Just ex1r => (weak dr (assert_smaller app (AppExpr ex1r ex2))) <|> (Just (AppExpr ex1r ex2))
     Nothing   => Nothing
  weakApp dr e = idris_crash ("weakApp " ++ (show e))

  reduce_to_whnf : DeltaRules -> Expr -> Expr
  reduce_to_whnf dr ex = case (weak dr ex) of
                                Just exr  => reduce_to_whnf dr (assert_smaller ex exr)
                                Nothing   => ex
