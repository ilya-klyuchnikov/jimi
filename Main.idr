module Main

import Tokenizer
import Parser
import AST

tryParse : String -> IO ()
tryParse source =
  do
    tokenization <- pure (tokenizeS source)
    putStrLn ("Tokenization Rest: " ++ (snd tokenization))
    parsing <- pure (parseDefs (fst tokenization))
    putStrLn "TDefs: "
    putStrLn (show (fst parsing))
    putStrLn "VDefs: "
    putStrLn (show (fst (snd parsing)))
    putStrLn "Parsing Rest: "
    putStrLn (show (snd (snd parsing)))

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
