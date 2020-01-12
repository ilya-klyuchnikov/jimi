module Parser

import AST
import Tokenizer

%default total

PInput : Type
PInput = List Token

PResult : Type -> Type
PResult a = (Maybe a, PInput)

Parser : Type -> Type
Parser a = PInput -> PResult a

-- and now - the same - to repeat everything?
-- no -
-- piExpr - the start is determinator
-- lamExpr - the start is determinator
-- caseExpr - the start is determinator
-- funExpr - everything else

vars : List Token -> (List Variable, List Token)
vars ((Identifier n) :: rest) = let (vs, rest1) = vars rest
                                in ((Var n) :: vs, rest1)
vars input = ([], input)


mutual

  bindVar : List Token -> PResult TVariable
  -- typed Variable
  bindVar input@(Identifier v :: Operator ":" :: rest) = case parseExpr rest of
                                                               (Just e, rest') => (Just (TVar (Var v) e), (assert_smaller input rest'))
                                                               (_, _) => (Nothing, input)

  -- untyped Variable
  bindVar input@(Identifier v :: rest)                 = (Just (TVar (Var v) (SortExpr Star)), rest)
  bindVar input                                        = (Nothing, input)

  atomExpr : List Token -> PResult Expr
  -- literal
  atomExpr input@(Keyword "Int" :: rest)               = (Just (LitExpr IntType), rest)
  atomExpr input@(Num n :: rest)                       = (Just (LitExpr (LitInt n)), rest)
  -- typed Variable
  atomExpr input@(Identifier v :: Operator ":" :: rest) = case parseExpr rest of
                                                               (Just e, rest') => (Just (VarExpr (TVar (Var v) e)), (assert_smaller input rest'))
                                                               (_, _) => (Nothing, input)

  -- untyped Variable
  atomExpr input@(Identifier v :: rest)                 = (Just (VarExpr (TVar (Var v) (SortExpr Star))), rest)
  -- sort
  atomExpr input@(Operator "*" :: rest)                 = (Just (SortExpr Star), rest)
  atomExpr input@(Operator "||" :: rest)                = (Just (SortExpr Box), rest)
  -- unknown
  atomExpr input@(Operator "?" :: rest)                 = (Just Unknown, rest)

  atomExpr input@(Operator "(" :: rest)                 = case parseExpr rest of
                                                               (Just e, Operator ")" :: rest') => (Just e, rest')
                                                               (_, _) => (Nothing, input)
  atomExpr input                                        = (Nothing, input)

  appExpr : List Token -> PResult Expr
  appExpr input = case atomExpr input of
                      (Just e, rest') => let (es, rest'') = atomExprs (assert_smaller input rest') in (Just $ foldl AppExpr e es, rest'')
                      (_, _) => (Nothing, input)

  atomExprs : List Token -> (List Expr, List Token)
  atomExprs input = case atomExpr input of
                    (Just e, rest) => let (es, rest') = atomExprs (assert_smaller input rest) in (e :: es, rest')
                    (_, _) => ([], input)
  atomExprs [] = ([], [])

  -----------
  funExpr : List Token -> PResult Expr
  funExpr input = case appExpr input of
                      (Just e, rest') => let (es, rest'') = arrowAppExprs (assert_smaller input rest') in (Just $ mkFun e es, rest'')
                      (_, _) => (Nothing, input)
                    where
                      mkFun : Expr -> List Expr -> Expr
                      mkFun e [] = e
                      mkFun e  (e' :: es') = PiExpr (TVar Anonymous e) (mkFun e' es')

  arrowAppExprs : List Token -> (List Expr, List Token)
  arrowAppExprs input@(Operator "->" :: rest)  = case appExpr rest of
                                                      (Just e, rest') => let (es, rest'') = arrowAppExprs (assert_smaller input rest') in (e :: es, rest'')
                                                      (_, _) => ([], input)
  arrowAppExprs input = ([], input)

  lamExpr : List Token -> PResult Expr
  lamExpr input = case bindVar input of
                      (Just bv, rest1) =>
                          case commaBindVars (assert_smaller input rest1) of
                            (vs, Operator "." :: rest2) =>  case parseExpr (assert_smaller input rest2) of
                              (Just body, rest3) => (Just $ foldr LamExpr body (bv :: vs), rest3)
                              (_, _) => (Nothing, input)
                            (_, _) => (Nothing, input)
                      (_, _) => (Nothing, input)

  piExpr : List Token -> PResult Expr
  piExpr input = case bindVar input of
                      (Just bv, rest1) =>
                          case commaBindVars (assert_smaller input rest1) of
                            (vs, Operator "." :: rest2) =>  case parseExpr (assert_smaller input rest2) of
                              (Just body, rest3) => (Just $ foldr PiExpr body (bv :: vs), rest3)
                              (_, _) => (Nothing, input)
                            (_, _) => (Nothing, input)
                      (_, _) => (Nothing, input)

  commaBindVars : List Token -> (List TVariable, List Token)
  commaBindVars input@(Operator "," :: rest) = case bindVar rest of
                                              (Just v, rest') => let (vs, rest'') = commaBindVars (assert_smaller input rest') in (v :: vs, rest'')
                                              (_, _) => ([], input)
  commaBindVars input = ([], input)

  caseExpr : List Token -> PResult Expr
  caseExpr input = case parseExpr input of
                      (Just e, Keyword "of" :: Operator "{" :: rest1) =>
                          case alts (assert_smaller input rest1) of
                            (Just as, Operator "}" :: Operator ":" :: rest2) => case parseExpr (assert_smaller input rest2) of
                                (Just tp, rest3) => (Just $ CaseExpr e as tp, rest3)
                                (_, _) => (Nothing, input)
                            (Just as, Operator "}" :: rest2) => (Just $ CaseExpr e as Unknown, rest2)
                            (_, _) => (Nothing, input)
                      (_, _) => (Nothing, input)

  alts : List Token -> PResult (List CaseAlt)
  alts input = case alt input of
                 (Just a, rest1) => let (as, rest2) = semicolonCaseAlts (assert_smaller input rest1)
                                    in (Just (a :: as), rest2)
                 (_, _) => (Nothing, input)

  semicolonCaseAlts : List Token -> (List CaseAlt, List Token)
  semicolonCaseAlts input@(Operator ";" :: rest1) = case alt rest1 of
                                          (Just a, rest2) => let (as, rest3) = semicolonCaseAlts (assert_smaller input rest2)
                                                             in (a :: as, rest3)
                                          (_, _) => ([], input)
  semicolonCaseAlts input = ([], input)

  alt : List Token -> PResult CaseAlt
  alt input = case bindVar input of
                (Just tc, rest1) => case vars rest1 of
                  (vs, Operator "=>" :: rest2) => case parseExpr (assert_smaller input rest2) of
                    (Just e, rest3) => (Just $ Alt tc (map (\v => TVar v Unknown) vs) [] e, rest3)
                    (_, _) => (Nothing, input)
                  (_, _) => (Nothing, input)
                (_, _) => (Nothing, input)

  parseExpr : List Token -> PResult Expr
  -- end of input -
  parseExpr [] = (Nothing, [])
  -- pi-expr -- TODO - rest of pi
  parseExpr (Operator "|~|" :: rest)  = piExpr rest
  parseExpr (Operator "\\/" :: rest)  = piExpr rest

  parseExpr (Operator "\\" :: rest)   = lamExpr rest
  parseExpr (Operator "/\\" :: rest)  = lamExpr rest
  -- case-expr -- TODO - rest of case
  parseExpr (Keyword "case" :: rest)  = caseExpr rest
  -- functional type
  parseExpr input = funExpr input

mutual
  semiBindVars : List Token -> (List TVariable, List Token)
  semiBindVars input@(Operator ";" :: rest) = case bindVar rest of
                                              (Just v, rest') => let (vs, rest'') = semiBindVars (assert_smaller input rest') in (v :: vs, rest'')
                                              (_, _) => ([], input)
  semiBindVars input = ([], input)

  parseTDecl : List Token -> PResult TDeclaration
  parseTDecl input@(Keyword "data" :: rest) =
    case bindVar rest of
      (Just bv, (Operator "=") :: (Operator "{") :: rest1) =>
        case bindVar rest1 of
          (Just bv', rest2) => case semiBindVars rest2 of
            (bvs', Operator "}" :: rest3) => (Just $ TDecl bv (bv' :: bvs'), rest3)
            (_, _) => (Nothing, input)
          (_, _) => (Nothing, input)
      (_, _) => (Nothing, input)
  parseTDecl input = (Nothing, input)

parseVDecl : List Token -> PResult VDeclaration
parseVDecl input@(Keyword "let" :: rest) =
  case bindVar rest of
    (Just bv, (Operator "=") :: rest1) =>
      case parseExpr rest1 of
        (Just e, rest2) => (Just $ VDecl bv e, rest2)
        (_, _) => (Nothing, input)
    (_, _) => (Nothing, input)
parseVDecl input = (Nothing, input)

parseDefs : List Token -> (List TDeclaration, List VDeclaration, List Token)
parseDefs input =
  case parseTDecl input of
    (Just tdecl, rest1) => let (tdecls, vdecls, rest2) = parseDefs (assert_smaller input rest1)
                           in  (tdecl :: tdecls, vdecls, rest2)
    (_, _) => case parseVDecl input of
                (Just vdecl, rest1) => let (tdecls, vdecls, rest2) = parseDefs (assert_smaller input rest1)
                                       in  (tdecls, vdecl :: vdecls, rest2)
                (_, _) => ([], [], input)

export
ParseResult : Type
ParseResult = (List TDeclaration, List VDeclaration)

export
parse : List Token -> ParseResult
parse tokens =
  case parseDefs tokens of
    (tDecls, vDecls, []) =>
      (tDecls, vDecls)
    (_, _, rTokens) =>
      idris_crash ("Unconsumed tokens: " ++ (show rTokens))

export
tDefs : ParseResult -> List TDeclaration
tDefs = fst

export
vDefs : ParseResult -> List VDeclaration
vDefs = snd
