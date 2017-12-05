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
processFile filename (Left err)
  = idris_crash ("cannot read file")
processFile filename (Right text)
  = tryParse text

main : IO ()
main = do
        filename <- pure "prelude.jimi"
        textOrError <- readFile filename
        processFile filename textOrError
