module Tokens

%default total

public export
record Tokens where
  constructor MkTokens
  commentLine    : String
  identStart     : Char -> Bool
  identChar      : Char -> Bool
  numStart       : Char -> Bool
  numChar        : Char -> Bool
  keywords       : List String
  operators      : List String


jimi : Tokens
jimi =
  MkTokens
    jimiCommentLine
    jimiIdentStart
    jimiIdentChar
    jimiNumStart
    jimiNumChar
    jimiKeywords
    jimiOperators
  where
    jimiCommentLine : String
    jimiCommentLine = "--"

    jimiIdentStart : Char -> Bool
    jimiIdentStart c = isAlpha c || (c == '_')

    jimiIdentChar : Char -> Bool
    jimiIdentChar c = isAlphaNum c || (c `elem` (cast "_'"))

    jimiNumStart : Char -> Bool
    jimiNumStart = isDigit

    jimiNumChar : Char -> Bool
    jimiNumChar = isDigit

    jimiKeywords : List String
    jimiKeywords = ["case", "data", "letrec", "type", "import", "in", "let", "of", "at", "Int"]

    jimiOperators : List String
    jimiOperators =
      ["=>", "=", "::", ":", ";", "\\/", "\\", "->", "/\\", "|~|", ".", ",", "*", "||", "{", "}", "(", ")"]

export
tokens : Tokens
tokens = jimi
