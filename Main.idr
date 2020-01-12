module Main

import Tokenizer
import Parser
import AST

processText : String -> IO ()
processText text =
  do
    defs <- pure (parse (tokenizeS text))
    putStrLn "TDefs: "
    traverse (putStrLn . show) (tDefs defs)
    putStrLn "VDefs: "
    traverse (putStrLn . show) (vDefs defs)
    pure ()

processFile : String -> IO ()
processFile "jimi" =
  pure ()
processFile filename =
  do
    putStrLn (">> Processing " ++ filename)
    (Right text) <- readFile filename
      | (Left err) => idris_crash (show err)
    processText text

main : IO ()
main =
  do
    (_ :: filenames) <- getArgs
    traverse processFile filenames
    pure ()
