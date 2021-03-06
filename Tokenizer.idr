module Tokenizer

import Tokens

%default total

Chars : Type
Chars = List Char

ops : List Chars
ops = map (cast {to = Chars}) (operators tokens)

kws : List String
kws = keywords tokens

firstOps : List Char
firstOps = nub $ catMaybes $ map head' ops

isIdentStart : Char -> Bool
isIdentStart = identStart tokens

isIdentChar : Char -> Bool
isIdentChar = identChar tokens

isOperatorStart : Char -> Bool
isOperatorStart c = c `elem` firstOps

isNumStart : Char -> Bool
isNumStart = numStart tokens

isNumChar : Char -> Bool
isNumChar = numChar tokens

public export
data Token = Num String | Keyword String | Identifier String | Operator String

export
Show Token where
  show (Num s) =
    "Num " ++ s
  show (Keyword s) =
    "Keyword " ++ s
  show (Identifier s) =
    "Identifier " ++ s
  show (Operator s) =
    "Operator " ++ s

data Dispatch
  = SpaceStart
  | OperatorStart
  | IdentifierStart
  | NumStart
  | UnknownStart

dispatch : Char -> Dispatch
dispatch c =
  if isSpace c then SpaceStart
  else if isOperatorStart c then OperatorStart
  else if isIdentStart c then IdentifierStart
  else if isNumStart c then NumStart
  else UnknownStart

Input : Type
Input = List Char

Result : Type
Result = (List Token, Input)

ResultS : Type
ResultS = (List Token, String)


operator   : Chars -> Maybe (Token, Chars)
operator   cs = op ops where
  op : (operators: List Chars) -> Maybe (Token, Chars)
  op [] = Nothing
  op (op1 :: ops1) = if op1 `isPrefixOf` cs
                     then let token = Operator (cast op1)
                              rest = drop (length op1) cs
                          in  Just (token, rest)
                     else op ops1

inComment : (input : Input) -> Input
inComment = dropWhile (not . isNL)

skipSpaces : Chars -> Chars
skipSpaces = dropWhile isSpace

identifier : Char -> Chars -> (Token, Chars)
identifier c cs =
  let
    (parsed, rest) = span isIdentChar cs
    idString = cast {to=String} (c :: parsed)
    token = if idString `elem` kws then Keyword idString else Identifier idString
  in
    (token, rest)

num : Char -> Chars -> (Token, Chars)
num c cs =
  let
    (parsed, rest) = span isNumChar cs
    numString = cast {to=String} (c :: parsed)
    token = Num numString
  in
    (token, rest)


-- space -> operator -> num -> idenifier
loop : (input : Input) -> (acc : List Token) -> Result
loop [] acc = (reverse acc, [])
loop cs@('-' :: '-' :: cs') acc = let rest = (inComment cs')
                                  in loop (assert_smaller cs rest) acc
loop cs@(c' :: cs') acc =
  case dispatch c' of
    SpaceStart =>
      let
        rest = (skipSpaces cs')
      in
        loop (assert_smaller cs rest) acc
    OperatorStart =>
      case operator cs of
        Nothing =>
          (reverse acc, cs)
        Just (tk, rest) =>
          loop (assert_smaller cs rest) (tk :: acc)
    NumStart =>
      let
        (tk, rest) = num c' cs'
      in
        loop (assert_smaller cs rest) (tk :: acc)
    IdentifierStart =>
      let
        (tk, rest) = identifier c' cs'
      in
        loop (assert_smaller cs rest) (tk :: acc)
    UnknownStart =>
      (reverse acc, cs)

tokenize : Input -> Result
tokenize input = loop input []

export
tokenizeS : String -> (List Token)
tokenizeS input =
  case tokenize (cast input) of
    (tokens, []) =>
      tokens
    (_, rest) =>
      idris_crash ("Unconsumed input: " ++ cast rest)
