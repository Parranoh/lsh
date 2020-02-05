module Main where

import Prelude
import qualified Lambda as L--ambda
import Text.Read (readMaybe)
import Data.Char (toLower)
import Data.List (isPrefixOf)
import Control.Monad (when, unless)
import Control.Monad.Trans.Class (lift)
import qualified Control.Monad.Trans.State.Strict as S--tate
import qualified System.Console.Haskeline as H--askeline
import qualified System.Console.Haskeline.Completion as H.C--ompletion

data Command
  = Check Form L.LExpr
  | Let String L.LExpr
  | NF L.LExpr
  | Eager L.LExpr
  | Print [String]
  | Reduce L.LExpr
  | Unchurch L.LExpr
  | Help
  | Quit
  deriving (Eq, Show)

data Form
  = WeakHeadNormalForm
  | NormalForm
  deriving (Show, Eq)

type StateM = S.StateT L.LDict IO

main :: IO ()
main = do
    _ <- S.runStateT (H.runInputT settings startup) L.empty
    return ()
  where
    settings :: H.Settings StateM
    settings = H.setComplete varComplete H.defaultSettings
      where
        varComplete :: H.C.CompletionFunc StateM
        varComplete = H.C.completeWordWithPrev Nothing " \t()>=+-*/×÷<:"
          (\prev word -> case prev of
            "" -> case word of
              "" -> return cmds
              "c" -> return $ map H.C.simpleCompletion ["c", "cw", "cn"]
              "cw" -> return [H.C.simpleCompletion "cw"]
              "cn" -> return [H.C.simpleCompletion "cn"]
              (cmd:_) -> if cmd `elem` "clnprhq"
                         then return [H.C.simpleCompletion [cmd]]
                         else return cmds
            _  -> do
              knownVars <- fmap L.keys S.get
              let fittingVars = filter (word `isPrefixOf`) knownVars
                  comps = map H.C.simpleCompletion fittingVars
              return comps)
        cmds :: [H.C.Completion]
        cmds = map H.C.simpleCompletion ["c","cw","cn","l","n","p","r","h","q"]

    startup :: H.InputT StateM ()
    startup = do
      term <- H.haveTerminalUI
      when term $
        H.outputStrLn greeting
      pcsLn term

    pcsLn :: Bool -> H.InputT StateM ()
    pcsLn term = go
      where
        go = do
          input <- H.getInputLine (if term then "λ " else "")
          case input of
            Nothing -> return ()
            Just line -> case parse line of
              Right cmd ->
                if cmd == Quit
                then return ()
                else do
                  dict <- lift S.get
                  let (dict', out) = exec dict cmd
                  unless (null out) $
                    H.outputStrLn out
                  lift $ S.put dict'
                  go
              Left err -> do
                unless (null err) $
                  H.outputStrLn err
                go

parse :: String -> Either String Command
parse "" = Left ""
parse (cmd:args) = case toLower cmd of
  'l' -> let (v,r) = span (`notElem` "= ") . dropWhile (== ' ') $ args
         in case v of
           "" -> Left "Error: Emtpy `l` command"
           _  -> case dropWhile (/= '=') r of
             ('=':rhs) -> maybe
                 (Left "Error: Malformed lambda in rhs of `l` command")
                 (Right . Let v)
               . readMaybe $ rhs
             _         -> Left "Error: Missing `=` in `l` command"
  'n' -> maybe
      (Left "Error: Malformed lambda in `n` command")
      (Right . NF)
    . readMaybe $ args
  'e' -> maybe
      (Left "Error: Malformed lambda in `e` command")
      (Right . Eager)
    . readMaybe $ args
  'p' -> Right . Print . words $ args
  'r' -> maybe
      (Left "Error: Malformed lambda in `r` command")
      (Right . Reduce)
    . readMaybe $ args
  'u' -> maybe
      (Left "Error: Malformed lambda in `u` command")
      (Right . Unchurch)
    . readMaybe $ args
  'h' -> Right Help
  'q' -> Right Quit
  'c' -> case args of
    ('n':se) -> maybe
        (Left "Error: Malformed lambda in `c` command")
        (Right . Check NormalForm)
      . readMaybe $ se
    ('w':se) -> maybe
        (Left "Error: Malformed lambda in `c` command")
        (Right . Check WeakHeadNormalForm)
      . readMaybe $ se
    _        -> maybe
        (Left "Error: Malformed lambda in `c` command")
        (Right . Check WeakHeadNormalForm)
      . readMaybe $ args
  _          -> Left "Error: Unknown command"

exec :: L.LDict -> Command -> (L.LDict, String)
exec d Help = (d, help)
exec d (Check WeakHeadNormalForm e) =
  let d' = L.insertIt e d
  in (d', if L.isWhnf d e then "Is WHNF" else "Not WHNF")
exec d (Check NormalForm e) =
  let d' = L.insertIt e d
  in (d', if L.isNf d e then "Is NF" else "Not NF")
exec d (Reduce e) =
  let d' = L.insertIt (L.toWhnf d e) d
  in (d', L.makeWhnf d e)
exec d (NF e) =
  let d' = L.insertIt (L.toNf d e) d
  in (d', L.makeNf d e)
exec d (Eager e) =
  let d' = L.insertIt (L.toNf d e) d
  in (d', L.makeEager d e)
exec d (Unchurch e) = case L.unchurch d e of
  Just e' -> let d' = L.insertIt e' d
             in (d', show e')
  _       -> (d, "Error: Result is not a Church numeral")
exec d (Let v e) = case L.insert v e d of
  Left err -> (d, err)
  Right d' -> let Just e' = L.lookup v d'
                  d''     = L.insertIt e' d'
              in (d'', "")
exec d (Print []) = (d, show d)
exec d (Print vs) = (d', show fd)
  where
    d' = case L.elemIfSingleton fd of
      Just e -> L.insertIt e d
      _      -> d
    fd = L.filter (`elem` vs) d
exec d cmd = (d, show cmd)

greeting :: String
greeting = "λsh\nFor help type `h`."
help :: String
help = "For help type `h`."
