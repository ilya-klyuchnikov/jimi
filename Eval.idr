module Eval

import AST
import TermSupport
import Reduce

%access public export

mutual
  eval : DeltaRules -> Expr -> Maybe Expr
  eval dr ex = let redexinf = redex dr ex
                   reduced = (reduceRedex dr redexinf ex)
               in
                  if (isSomeRedex redexinf)
                  then (eval dr reduced) <|> (Just reduced)
                  else if (isApp ex)
                  then evalApp dr ex
                  else Nothing

  evalApp : DeltaRules -> Expr -> Maybe Expr
  evalApp dr (AppExpr ex1 ex2) =
    case (eval dr ex1) of
      Just ex1r => (eval dr (AppExpr ex1r ex2)) <|> (Just (AppExpr ex1r ex2))
      Nothing => case (eval dr ex2) of
                    Just ex2r   => Just (AppExpr ex1 ex2r)
                    Nothing     => Nothing
  evalApp dr e = idris_crash ("evalApp: " ++ show e)

-- Reducing using the normal strategy until a "eval" head normal form is reached
reduce_to_mnf : DeltaRules -> Expr -> Expr
reduce_to_mnf dr ex = case (eval dr ex) of
                        Just exr   => exr
                        Nothing    => ex


mutual
  strong : DeltaRules -> Expr -> Maybe Expr
  strong dr ex = let redexinf = redex dr ex
                     reduced  = (reduceRedex dr redexinf ex)
                 in
                   if not $ or [isNoRedex redexinf, isBetaRedex redexinf]
                   then (strong dr reduced) <|> (Just reduced)
                   else if isBetaRedex redexinf
                   then let (AppExpr  (LamExpr tv ex1) ex2)=ex
                            breduced =  applySStrongSubst (Sub tv ex2) ex1
                        in (strong dr breduced) <|> (Just breduced)
                   else if isApp ex
                   then strongApp dr ex
                   else if isLam ex
                   then strongLam dr ex
                   else Nothing

  strongApp : DeltaRules -> Expr -> Maybe Expr
  strongApp dr ex@(AppExpr ex1 ex2) =
    case strong dr ex1 of
      Just ex1r => (strong dr (AppExpr ex1r ex2)) <|> (Just $ AppExpr ex1r ex2)
      Nothing   => case (strong dr ex2) of
                    Just ex2r => Just $ AppExpr ex1 ex2r
                    Nothing   => Nothing

  strongApp dr e = idris_crash ("strongApp: " ++ show e)

  strongLam : DeltaRules -> Expr -> Maybe Expr
  strongLam dr (LamExpr (TVar var exv) ex)
    = let mexvr = strong dr exv
          mexr  = strong dr ex
      in
        if (isNothing mexvr) && (isNothing mexr)
        then Nothing
        else
        do {exvr <- mexvr  <|> (Just exv)
            ;exr <- mexr  <|> (Just ex)
            ;pure $ LamExpr (TVar var exvr) exr}
