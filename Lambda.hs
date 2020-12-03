module Lambda
( LExpr ()
, makeNf
, toNf
, isNf
, makeWhnf
, toWhnf
, isWhnf
, makeEager
, unchurch
, LDict ()
, insert
, insertIt
, insertItVar
, empty
, lookup
, filter
, member
, notMember
, keys
, elemIfSingleton
) where

import Prelude hiding (lookup, filter)
import Data.Bifunctor (first)
import qualified Data.Set as S
import qualified Data.Map.Strict as M

data LExpr = Var String
           | App LExpr LExpr
           | Lam String LExpr

-- equivalence mod α conversion
instance Eq LExpr where
  Var v1      == Var v2      = v1  == v2
  l1 `App` r1 == l2 `App` r2 = l1  == l2 && r1 == r2
  Lam v1 e1   == Lam v2 e2   = e1' == e2'
    where
      v'  = newVar "" (free e1 `S.union` free e2)
      e1' = subst (Var v') v1 e1
      e2' = subst (Var v') v2 e2
  _           == _           = False

instance Show LExpr where
  showsPrec _ (Var v) = showString v
  showsPrec p (App e e') = showParen (p > 2)
    (showsPrec 2 e . showString " " . showsPrec 3 e')
  showsPrec p (Lam v e) = showParen (p > 1) (
      (if p /= 1 then showString "\\" else id)
      . showString v
      . (case e of {(Lam _ _) -> showString " "; _ -> showString " -> "})
      . showsPrec 1 e
    )

instance Read LExpr where
  readsPrec d p =  readParen (d > app_prec)
                   (\r -> [(e,s) |
                          (es@(_:_:_), s) <- readAppList r,
                          let e = foldl1 App es]) p

                ++ readParen (d > lam_prec)
                   (\r -> [(e,u) |
                          ("\\",s) <- lex r,
                          (vs,'-':'>':t) <- [span (/= '-') s],
                          vars@(_:_) <- [words vs],
                          all validVar vars,
                          (body,u) <- readsPrec (lam_prec+1) t,
                          let e = foldr Lam body vars]) p

                ++ readParen False
                   (\r -> [(Var var,s) |
                          (v@(_:_),s) <- lex r,
                          let var = readNum v,
                          validToken var]) p

    where
      lam_prec = 0
      app_prec = 1

      readNum :: String -> String
      readNum ('_':cs@(_:_)) = '-':cs
      readNum cs             = cs

      readAppList :: ReadS [LExpr]
      readAppList r = do
        (e, s) <- readsPrec (app_prec+1) r
        let l = readAppList s
            list = case l of
              [] -> [([],s)]
              _  -> l
        (es,t) <- list
        return (e:es,t)

validVar :: String -> Bool
validVar (s:ss)
    | letter s && all alphaNum ss = True
  where
    letter c   = c `S.member` letters
    letters    = S.fromList ['a'..'z']

    alphaNum c = letter c || number [c] || c `S.member` other
    other      = S.fromList $ '\'':['A'..'Z']
validVar "_" = True
validVar _   = False

validToken :: String -> Bool
validToken "_" = False
validToken v
  | validVar v = True
  | symbol   v = True
  | number   v = True
  | otherwise  = False

binOp :: String -> Bool
binOp = flip elem ["+","-","*","×","/","÷","=","<",">"]

boolean :: String -> Bool
boolean = flip elem ["True", "False"]

churchNum :: String -> Bool
churchNum ('C':n@(_:_)) = number n
churchNum _             = False

symbol :: String -> Bool
symbol v = binOp v || boolean v || churchNum v || v `elem` [":","If","It","Y","S","K","I"]

number :: String -> Bool
number ""     = False
number (c:cs) = c `elem` "-" ++ ['0'..'9'] && all (`elem` ['0'..'9']) cs

expr :: LExpr
expr = read "\\x z -> y (\\x -> x y) (\\y -> x y)"

freeBound :: LExpr -> (S.Set String, S.Set String)
freeBound (Var x)     = (S.singleton x, S.empty)
freeBound (App e1 e2) = (fe1 `S.union` fe2, be1 `S.union` be2)
  where
    (fe1, be1) = freeBound e1
    (fe2, be2) = freeBound e2
freeBound (Lam v e)
    | v `S.member` fe = (S.delete v fe, S.insert v be)
    | otherwise       = p
  where p@(fe, be) = freeBound e

free :: LExpr -> S.Set String
free (Var v)
  | symbol v  = S.empty
  | number v  = S.empty
  | otherwise = S.singleton v
free (App e e') = free e `S.union` free e'
free (Lam v e)
  | v `S.member` fe = S.delete v fe
  | otherwise       = fe
  where
    fe = free e

bound :: LExpr -> S.Set String
bound = snd . freeBound

newVar :: String -> S.Set String -> String
newVar v vs = head . dropWhile (`S.member` vs) . tail . iterate (++ "'") $ v

subst :: LExpr -> String -> LExpr -> LExpr
subst m x = go
  where
    go (Var v)   | x == v    = m
                 | otherwise = Var v
    go (App l r) = App (go l) (go r)
    go (Lam v e) | v == x    = Lam v e
                 | x `S.notMember` free e = Lam v e
                 | v `S.notMember` free m = Lam v (go e)
                 | otherwise = let z = newVar v (free m)
                               in go (Lam z (subst (Var z) v e))

substAlpha :: LExpr -> String -> LExpr -> (Bool, LExpr)
substAlpha m x = go
  where
    go (Var v)   | x == v    = (False,  m)
                 | otherwise = (False, Var v)
    go (App l r)
      | al        = (True,  App l' r)
      | ar        = (True,  App l  r')
      | otherwise = (False, App l' r')
      where
        (al, l') = go l
        (ar, r') = go r
    go (Lam v e) | v == x = (False, Lam v e)
                 | x `S.notMember` free e = (False, Lam v e)
                 | v `S.notMember` free m = (ae, Lam v e')
                 | otherwise = let z = newVar v (free m `S.union` free e)
                               in (True, Lam z (subst (Var z) v e))
                 where
                   (ae, e') = go e

church :: Int -> LExpr
church n = Lam "f" $ Lam "x" $ iterate (Var "f" `App`) (Var "x") !! n

data Reduction
  = None
  | Start
  | Alpha
  | Beta
  | Delta
  | Definition String
  deriving (Show, Eq)

normalOrder :: LDict -> LExpr -> (Reduction, LExpr)
normalOrder d = go
  where
    -- delta reducible expressions
    go ((Var "+" `App` Var a) `App` Var b)
      | number a && number b =
          (Delta, Var . show $ (read a + read b :: Integer))
    go ((Var "-" `App` Var a) `App` Var b)
      | number a && number b =
          (Delta, Var . show $ (read a - read b :: Integer))
    go ((Var "*" `App` Var a) `App` Var b)
      | number a && number b =
          (Delta, Var . show $ (read a * read b :: Integer))
    go ((Var "×" `App` Var a) `App` Var b)
      | number a && number b =
          (Delta, Var . show $ (read a * read b :: Integer))
    go ((Var "/" `App` Var a) `App` Var b)
      | number a && number b =
          (Delta, Var . show $ (read a `div` read b :: Integer))
    go ((Var "÷" `App` Var a) `App` Var b)
      | number a && number b =
          (Delta, Var . show $ (read a `div` read b :: Integer))
    go ((Var "=" `App` Var a) `App` Var b)
      | number a && number b = (Delta, Var . show $ a == b)
    go ((Var "<" `App` Var a) `App` Var b)
      | number a && number b = (Delta, Var . show $ a < b)
    go ((Var ">" `App` Var a) `App` Var b)
      | number a && number b = (Delta, Var . show $ a > b)
    go (((Var "If" `App` Var "True")  `App` t) `App` _) = (Delta, t)
    go (((Var "If" `App` Var "False") `App` _) `App` e) = (Delta, e)

    -- variable definitions
    go (Var "Y") = (Definition "Y",
      Lam "x" $ (
          Lam "y" $
              Var "x"
            `App` (
                Var "y"
              `App`
                Var "y"))
        `App` (
          Lam "y" $
               Var "x"
            `App` (
                Var "y"
              `App`
                Var "y")))
    go (Var "S") = (Definition "S",
      Lam "f" $ Lam "g" $ Lam "x" $
          (Var "f" `App` Var "x")
        `App`
          (Var "g" `App` Var "x"))
    go (Var "K") = (Definition "K", Lam "x" $ Lam "_" $ Var "x")
    go (Var "I") = (Definition "I", Lam "x" $ Var "x")
    go (Var cn)
      | churchNum cn = (Definition cn, church n)
      where
        n :: Int
        n = read . tail $ cn

    go (Var v) = case me of
      Just e -> (Definition v, e)
      _      -> (None, Var v)
      where
        me = lookup v d

    -- other
    go (Lam v l `App` r)
      | al        = (Alpha, Lam v l' `App` r)
      | otherwise = (Beta, l')
      where
        (al, l') = substAlpha r v l
    go (l `App` r) = case go l of
      (None, _) -> (l `App`) <$> go r
      (rl, l')  -> (rl, l' `App` r)
    go (Lam v e) = Lam v <$> go e

applicativeOrder :: LDict -> LExpr -> (Reduction, LExpr)
applicativeOrder d = go
  where
    -- delta reducible expressions
    go ((Var "+" `App` Var a) `App` Var b)
      | number a && number b =
          (Delta, Var . show $ (read a + read b :: Integer))
    go ((Var "-" `App` Var a) `App` Var b)
      | number a && number b =
          (Delta, Var . show $ (read a - read b :: Integer))
    go ((Var "*" `App` Var a) `App` Var b)
      | number a && number b =
          (Delta, Var . show $ (read a * read b :: Integer))
    go ((Var "×" `App` Var a) `App` Var b)
      | number a && number b =
          (Delta, Var . show $ (read a * read b :: Integer))
    go ((Var "/" `App` Var a) `App` Var b)
      | number a && number b =
          (Delta, Var . show $ (read a `div` read b :: Integer))
    go ((Var "÷" `App` Var a) `App` Var b)
      | number a && number b =
          (Delta, Var . show $ (read a `div` read b :: Integer))
    go ((Var "=" `App` Var a) `App` Var b)
      | number a && number b = (Delta, Var . show $ a == b)
    go ((Var "<" `App` Var a) `App` Var b)
      | number a && number b = (Delta, Var . show $ a < b)
    go ((Var ">" `App` Var a) `App` Var b)
      | number a && number b = (Delta, Var . show $ a > b)
    go (((Var "If" `App` Var "True")  `App` t) `App` _) = (Delta, t)
    go (((Var "If" `App` Var "False") `App` _) `App` e) = (Delta, e)

    -- variable definitions
    go (Var cn)
      | churchNum cn = (Definition cn, church n)
      where
        n :: Int
        n = read . tail $ cn
    go (Var v) = case me of
      Just e -> (Definition v, e)
      _      -> (None, Var v)
      where
        me = lookup v d

    -- other
    go (l@(Lam v lb) `App` r) = case rr of
      None -> if al
              then (Alpha, Lam v l' `App` r)
              else (Beta, l')
      _    -> (rr, l `App` r')
      where
        (rr, r') = go r
        (al, l') = substAlpha r v lb
    go (l `App` r) = case go l of
      (None, _) -> (l `App`) <$> go r
      (rl, l')  -> (rl, l' `App` r)
    go (Lam v e) = Lam v <$> go e

(>>#) :: (a,b) -> (b -> (a,b)) -> (a,b)
(_,x) >># f = f x
infixl 1 >>#

reduce :: LDict -> LExpr -> [(Reduction, LExpr)]
reduce d = iterate (>># normalOrder d) . (,) Start

reduceEager :: LDict -> LExpr -> [(Reduction, LExpr)]
reduceEager d = iterate (>># applicativeOrder d) . (,) Start

isWhnf :: LDict -> LExpr -> Bool
isWhnf d = go
  where
    -- delta reducible
      -- binary operators are strict in both arguments
    go ((Var op `App` a) `App` b)
      | binOp op = twoStrict
      where
        twoStrict :: Bool
        twoStrict
          | not (number' a) && go a = True
          | not (number' b) && go b = True
          | otherwise               = False
        number' :: LExpr -> Bool
        number' (Var x) = number x
        number' _       = False
      -- ternary operator `If` is strict in first argument
    go (((Var "If" `App` c) `App` _) `App` _)
      | boolean' c = False
      | otherwise  = go c
      where
        boolean' (Var x) = boolean x
        boolean' _       = False

    -- substitute church numerals only if two args are supplied
    go (Var cn `App` _ `App` _)
      | churchNum cn = False

    -- beta reducible
    go (Var v)   = notMember v d && notElem v ["Y","S","K","I"]
    go (App l _) = case l of
      Lam _ _ -> False
      _       -> go l
    go (Lam _ _) = True

toWhnf :: LDict -> LExpr -> LExpr
toWhnf d = head . dropWhile (not . isWhnf d) . map snd . reduce d

makeWhnfList :: LDict -> LExpr -> [(Reduction, LExpr)]
makeWhnfList d = takeUntil (isWhnf d . snd) . reduce d

isNf :: LDict -> LExpr -> Bool
isNf d = (== None) . fst . normalOrder d

toNf :: LDict -> LExpr -> LExpr
toNf d = snd . last . makeNfList d

makeNfList :: LDict -> LExpr -> [(Reduction, LExpr)]
makeNfList d = takeWhile ((/= None) . fst) . reduce d

makeEagerList :: LDict -> LExpr -> [(Reduction, LExpr)]
makeEagerList d = takeWhile ((/= None) . fst) . reduceEager d

unchurch :: LDict -> LExpr -> Maybe LExpr
unchurch d e
  | number ue = Just . read $ 'C' : ue
  | otherwise = Nothing
  where
    e' = e `App` (Var "+" `App` Var "1") `App` Var "0"
    ue = show . toWhnf d $ e'

takeUntil :: (a -> Bool) -> [a] -> [a]
takeUntil p = go
  where
    go [] = []
    go (x:xs) | p x = [x]
              | otherwise = x : go xs

breakOne :: (a -> Bool) -> [a] -> ([a], [a])
breakOne p = go
  where
    go [] = ([], [])
    go (x:xs) | p x = ([x], xs)
              | otherwise = first (x:) $ go xs

newtype RedList = RedList [(Reduction, LExpr)]

instance Show RedList where
  showsPrec _ (RedList l) = foldl f id l
    where
      f s (r, e) =
        (
          if s "" == ""
          then id
          else s . showChar '\n'
        )
        . showRed r
        . showChar '\t'
        . shows e
      showRed :: Reduction -> ShowS
      showRed Alpha          = showString "<-α->\t"
      showRed Beta           = showString "--β->\t"
      showRed Delta          = showString "--δ->\t"
      showRed (Definition v) = showString "(def "
                             . showString v
                             . showString ") ≡"
      showRed _              = showChar '\t'

makeNf :: LDict -> LExpr -> String
makeNf d e = shows (RedList notWhnf) .
                showString "\n\t=== Reached WHNF ===" .
                (
                  if null whnf
                  then id
                  else showChar '\n'
                ) .
                shows (RedList whnf) $
                ""
  where
    (notWhnf, whnf) = breakOne (isWhnf d . snd) . makeNfList d $ e

makeWhnf :: LDict -> LExpr -> String
makeWhnf d = show . RedList . makeWhnfList d

makeEager :: LDict -> LExpr -> String
makeEager d e = shows (RedList notWhnf) .
                showString "\n\t=== Reached WHNF ===" .
                (
                  if null whnf
                  then id
                  else showChar '\n'
                ) .
                shows (RedList whnf) $
                ""
  where
    (notWhnf, whnf) = breakOne (isWhnf d . snd) . makeEagerList d $ e

newtype LDict = LDict (M.Map String LExpr)

instance Show LDict where
  showsPrec _ (LDict d) = foldl f id . M.toList $ d
    where
      f s (v, e)
        | s "" == "" =
            showString v
          . showString "\t:= "
          . shows e
        | otherwise =
            s
          . showChar '\n'
          . showString v
          . showString "\t:= "
          . shows e

empty :: LDict
empty = LDict M.empty

insert :: String -> LExpr -> LDict -> Either String LDict
insert var e (LDict d)
  | not (validVar var) || var == "_" = Left "Error: Invalid variable name"
  | null unknown = Right . LDict . M.insert var e' $ d
  | otherwise = Left $ "Error: Unknown variable name(s):" ++ unknown
  where
    e' = case M.lookup "It" d of
      Just it -> subst it "It" e
      _       -> e
    unknown = drop 1 . concatMap showIfInvalid . S.toList . free $ e'
    showIfInvalid v =
      if M.member v tmpD
      then ""
      else ", " ++ v
    tmpD = M.delete "It" . M.delete var $ d

insertIt :: LExpr -> LDict -> LDict
insertIt e (LDict d) = LDict $ M.insert "It" e d

insertItVar :: String -> LDict -> LDict
insertItVar = insertIt . Var

lookup :: String -> LDict -> Maybe LExpr
lookup v (LDict d) = M.lookup v d

filter :: (String -> Bool) -> LDict -> LDict
filter p (LDict d) = LDict $ M.filterWithKey (\k _ -> p k) d

member :: String -> LDict -> Bool
member v (LDict d) = M.member v d

notMember :: String -> LDict -> Bool
notMember v (LDict d) = M.notMember v d

keys :: LDict -> [String]
keys (LDict d) = M.keys d

elemIfSingleton :: LDict -> Maybe LExpr
elemIfSingleton (LDict d) = case M.elems d of
  [e] -> Just e
  _   -> Nothing
