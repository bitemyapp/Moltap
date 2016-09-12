{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wall #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Moltap.Util.Util
-- Copyright   :  (c) 2008 Twan van Laarhoven
-- License     :  GPL 2 or later
-- Maintainer  :  twanvl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Utility functions used throughout Moltap
--
--------------------------------------------------------------------------------

module Moltap.Util.Util where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Map            (Map)
import Data.Set            (Set)
import Data.List           (foldl', intersperse)
import Data.Char
import Data.Int
import Data.Word
import Control.Exception   ( throwIO
                           , ErrorCall(..)
                           , Exception(..)
                           , AsyncException(..)
                           , catch)
import Control.Monad.Trans (MonadIO(..))
import Control.Concurrent
import Prelude hiding      (catch)

#ifdef UNIX
import Data.Bits
import System.Posix.Files
#endif

{-
************************************************************************
*                                                                      *
\subsection[Utils-Hashing]{Utils for hashing}

Originally from ghc-7.10.3

*                                                                      *
************************************************************************
-}

-- | A sample hash function for Strings.  We keep multiplying by the
-- golden ratio and adding.  The implementation is:
--
-- > hashString = foldl' f golden
-- >   where f m c = fromIntegral (ord c) * magic + hashInt32 m
-- >         magic = 0xdeadbeef
--
-- Where hashInt32 works just as hashInt shown above.
--
-- Knuth argues that repeated multiplication by the golden ratio
-- will minimize gaps in the hash space, and thus it's a good choice
-- for combining together multiple keys to form one.
--
-- Here we know that individual characters c are often small, and this
-- produces frequent collisions if we use ord c alone.  A
-- particular problem are the shorter low ASCII and ISO-8859-1
-- character strings.  We pre-multiply by a magic twiddle factor to
-- obtain a good distribution.  In fact, given the following test:
--
-- > testp :: Int32 -> Int
-- > testp k = (n - ) . length . group . sort . map hs . take n $ ls
-- >   where ls = [] : [c : l | l <- ls, c <- ['\0'..'\xff']]
-- >         hs = foldl' f golden
-- >         f m c = fromIntegral (ord c) * k + hashInt32 m
-- >         n = 100000
--
-- We discover that testp magic = 0.
hashString :: String -> Int32
hashString = foldl' f golden
   where f m c = fromIntegral (ord c) * magic + hashInt32 m
         magic = fromIntegral (0xdeadbeef :: Word32)

golden :: Int32
golden = 1013904242 -- = round ((sqrt 5 - 1) * 2^32) :: Int32
-- was -1640531527 = round ((sqrt 5 - 1) * 2^31) :: Int32
-- but that has bad mulHi properties (even adding 2^32 to get its inverse)
-- Whereas the above works well and contains no hash duplications for
-- [-32767..65536]

-- | A sample (and useful) hash function for Int32,
-- implemented by extracting the uppermost 32 bits of the 64-bit
-- result of multiplying by a 33-bit constant.  The constant is from
-- Knuth, derived from the golden ratio:
--
-- > golden = round ((sqrt 5 - 1) * 2^32)
--
-- We get good key uniqueness on small inputs
-- (a problem with previous versions):
--  (length $ group $ sort $ map hashInt32 [-32767..65536]) == 65536 + 32768
--
hashInt32 :: Int32 -> Int32
hashInt32 x = mulHi x golden + x

-- hi 32 bits of a x-bit * 32 bit -> 64-bit multiply
mulHi :: Int32 -> Int32 -> Int32
mulHi a b = fromIntegral (r `shiftR` 32)
   where r :: Int64
         r = fromIntegral a * fromIntegral b

--------------------------------------------------------------------------------
-- * Sorted lists
--------------------------------------------------------------------------------

-- | Intersection, union and differences of sorted lists
--
--  > iud a b = (intersection, union, only in a, only in b)
iud :: Ord a => [a] -> [a] -> ([a],[a],[a],[a])
iud [] ys = ([],ys,[],ys)
iud xs [] = ([],xs,xs,[])
iud xxs@(x:xs) yys@(y:ys) = case compare x y of
    LT -> let (i,u,da,db) = iud xs yys in (i,x:u,x:da,db)
    EQ -> let (i,u,da,db) = iud xs ys  in (x:i,x:u,da,db)
    GT -> let (i,u,da,db) = iud xxs ys in (i,y:u,da,y:db)

--------------------------------------------------------------------------------
-- * Relations
--------------------------------------------------------------------------------

-- | A binary relation from @a@ to @a@
type Relation a = Map a [a]

-- | Symmetric closure of a relation
symmClose :: Ord a => Relation a -> Relation a
symmClose rel = Map.unionWith (++) rel $
                Map.fromListWith (++) [ (y,[x]) | (x,ys) <- Map.toList rel, y <- ys ]

-- | Reflexive closure of a relation
reflClose :: Ord a => [a] -> Relation a -> Relation a
reflClose worlds rel = Map.unionWith (++) rel (Map.fromList [ (x, [x]) | x <- worlds ] )

-- | (Reflexive-)transitive closure of a relation
transClose :: Ord a => Bool -> [a] -> Relation a -> Relation a
transClose refl worlds rel = Map.fromList [ (x, Set.toList (transCloseAt refl x rel)) | x <- worlds ]

-- | A single element from the (reflexive-)transitive closure
transCloseAt :: Ord a => Bool -> a -> Relation a -> Set a
transCloseAt refl xx rel = (if refl then cons else cons') Set.empty xx
 where cons seen x
         | x `Set.member` seen = seen
         | otherwise           = cons' (Set.insert x seen) x
       cons' seen x = foldl cons seen (Map.findWithDefault [] x rel)

--------------------------------------------------------------------------------
-- * ShowS
--------------------------------------------------------------------------------

-- | 'Concatenate' a list of @ShowS@s
catShows :: [ShowS] -> ShowS
catShows = foldr (.) id

-- | Show a list by applying a function to each element
showListWith :: (a -> ShowS) -> [a] -> ShowS
showListWith f = catShows . map f

-- | Show a list by applying a function to each element, and putting a separator between them
showListWithSep :: String -> (a -> ShowS) -> [a] -> ShowS
showListWithSep sep f = catShows . intersperse (showString sep) . map f

--------------------------------------------------------------------------------
-- * Strings
--------------------------------------------------------------------------------

-- | Escape a string for dot or json output
escapeString :: String -> String
escapeString str = '"' : esc str
  where
    esc []        = "\""
    esc ('\\':xs) = "\\\\" ++ esc xs
    esc ('"' :xs) = "\\\"" ++ esc xs
    esc ('\n':xs) = "\\n"  ++ esc xs
    esc (x   :xs) = x       : esc xs

--------------------------------------------------------------------------------
-- * Files
--------------------------------------------------------------------------------

-- | Turn a string into something that is safe to use as a filename.
--   The string will uniquely determine the filename.
toFileName :: String -> FilePath
toFileName xs = case splitAt 30 xs of
                  (ys,[]) -> toFileName' ys
                  (ys,zs) -> toFileName' ys ++ show (hashString zs)
  where
    toFileName' = concatMap mkSafe
    mkSafe '.'  = "zd"
    mkSafe '_'  = "zu"
    mkSafe ' '  = "_"
    mkSafe '|'  = "zp"
    mkSafe '&'  = "ze"
    mkSafe '~'  = "zt"
    mkSafe '/'  = "zs"
    mkSafe '\\' = "zb"
    mkSafe '<'  = "zl"
    mkSafe '>'  = "zg"
    mkSafe 'z'  = "zz"
    mkSafe x | isAlphaNum x = [x]
    mkSafe _    = "z_"

-- | Make a file readable to all users
makeFileReadable :: FilePath -> IO ()
#ifdef UNIX
makeFileReadable f = setFileMode f mode
  where mode = ownerReadMode  .|. ownerWriteMode .|.
               groupReadMode  .|. otherReadMode
#else
makeFileReadable _ = return ()
#endif

--------------------------------------------------------------------------------
-- * IO Monad
--------------------------------------------------------------------------------

-- | 'error' in the IO monad
errorIO :: MonadIO m => String -> m a
errorIO e = liftIO $ throwIO $ ErrorCall e

-- | Perform two actions in parallel, use the result from the one that finishes first.
-- stolen from
-- <http://www.haskell.org/pipermail/haskell-cafe/2005-January/008314.html>
parIO :: IO a -> IO a -> IO a
parIO a1 a2 = do
  m <- newEmptyMVar
  myThread <- myThreadId
  let handleExceptions io = catch io $ \e -> case e of
              ThreadKilled -> throwIO e          -- do let the thread be killed
              _            -> throwTo myThread e -- but catch all other exceptions
  c1 <- forkIO $ handleExceptions $ putMVar m =<< a1
  c2 <- forkIO $ handleExceptions $ putMVar m =<< a2
  r <- takeMVar m
  -- killThread blocks until the thread has been killed.  Therefore, we call
  -- killThread asynchronously in case one thread is blocked in a foreign
  -- call.
  forkIO $ killThread c1 >> killThread c2
  return r

-- | Run an action with a timeout (in microseconds)
timeout :: Int -> IO a -> IO (Maybe a)
timeout n a = parIO (Just `fmap` a) (threadDelay n >> return Nothing)

-- | Run an action with a timeout (in microseconds)
timeoutWith :: Int -> IO a -> IO a -> IO a
timeoutWith n failed a = parIO a (threadDelay n >> failed)
