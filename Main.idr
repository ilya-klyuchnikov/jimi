module Main

import Tokenizer
import Parser
import AST

tryParse : String -> IO ()
tryParse source =
  do
    defs <- pure (parse (tokenizeS source))
    putStrLn "TDefs: "
    traverse (putStrLn . show) (tDefs defs)
    putStrLn "VDefs: "
    traverse (putStrLn . show) (vDefs defs)
    pure ()

processFile : String -> (Either FileError String) -> IO ()
processFile filename (Left err) =
  idris_crash ("cannot read file")
processFile filename (Right text) =
  do
    putStrLn (">> Processing " ++ filename)
    tryParse text

main : IO ()
main =
  do
    filename1 <- pure "prelude.jimi"
    textOrError1 <- readFile filename1
    processFile filename1 textOrError1
    filename2 <- pure "prog.jimi"
    textOrError2 <- readFile filename2
    processFile filename2 textOrError2
