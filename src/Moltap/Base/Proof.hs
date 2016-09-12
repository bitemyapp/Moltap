{-# LANGUAGE FlexibleInstances, OverlappingInstances #-}

module Moltap.Base.Proof where

import qualified Data.Set as Set
import Data.Set (Set)
import Control.Monad.Error
import Control.Applicative
import Data.Monoid

import Moltap.Base.Syntax
import Moltap.Base.Agents

----------------------------------------------------------------
-- Sign
----------------------------------------------------------------

data Signed a
    = Pos a
    | Neg a
  deriving (Eq,Ord,Show)

instance Functor Signed where
    fmap f (Pos a) = Pos (f a)
    fmap f (Neg a) = Neg (f a)

instance Applicative Signed where
    pure = Pos
    Pos a <*> Pos b = Pos (a b)
    Pos a <*> Neg b = Neg (a b)
    Neg a <*> Pos b = Neg (a b)
    Neg a <*> Neg b = Pos (a b)

-- DEBUG:
instance Show a => Show (Signed [a]) where
      show (Pos _) = "+"
      show (Neg _) = "-"
--    show (Pos a) = concatMap (("\n+"++) . show) a
--    show (Neg a) = concatMap (("\n-"++) . show) a

-- | The sign of a signed value
sign :: Signed a -> Bool
sign (Pos _) = True
sign (Neg _) = False

-- | Flip a sign
flipSign :: Signed a -> Signed a
flipSign (Pos a) = Neg a
flipSign (Neg a) = Pos a

(+/-) :: Bool -> a -> Signed a
True  +/- a = Pos a
False +/- a = Neg a

----------------------------------------------------------------
-- Partial proofs
----------------------------------------------------------------

-- | Halve a proof,
--   A HalfProof for @a@ could be for instance @a|- ==> ... ==> goal@
-- 
--   Two HalfProofs can be connected to form a full proof, with the root @a |- a@.
type HalfProof = Signed [ProofPart]


data ProofPart
    = HProofNeg    Bool   Formula
    | HProofAnd           Formula Formula
    | HProofAndL          Formula
    | HProofAndR          Formula
    | HProofBoxP   Agents Formula
    | HProofBoxJ   Agents Formula
    | HProofBoxN   Agents Formula
    | HProofDropA
    | HProofSplitL        Formula
    | HProofSplitR        Formula
  deriving (Show)

----------------------------------------------------------------
-- Half proofs to proofs
----------------------------------------------------------------

-- | Terminate a proof in @false |- D@.
proofFalsum :: ProofPart -> Proof
proofFalsum pt = undefined--toProof pt (P0 P0_Truth)

-- | Terminate a proof in @G, a |- a, D@.
proofAssum :: Formula -> ProofPart -> ProofPart -> Proof
proofAssum = undefined


proof1 :: ProofPart -> Proof -> Proof
proof1 = undefined
--proof1 (HProofGoal _) = id
--proof1 (HProofNeg  p) = ProofNeg True . proof1 p

--moveBoxTop

--toProof :: Signed ProofPart -> ProofTree -> ProofTree
toProof []                  pr = pr
toProof (HProofAnd  a b:xs) pr = toProof xs $ P1 (P1_And a b) pr
--toProof (HProofNeg  st :xs) pr = toProof xs $ P1 (P1_Neg st)  pr
toProof (HProofBoxJ a t:xs) pr = undefined

--toProof sp pr = toProof' sp (runProof pr) pr
--toProof' sp pr

dupBox a [] = error "Can't dupBox"
dupBox a (x:xs) = undefined

----------------------------------------------------------------
-- Reverse proofs
----------------------------------------------------------------

data RProofStep0
    = R0_Goal  Formula
    | R0_Split 
data RProofStep1
    = R1_False
data RProofStep2
    = R2_Assume Formula

----------------------------------------------------------------
-- Combining proofs
----------------------------------------------------------------

-- | Combine @a |- b@ and @c |- d@ into @...@
proofAnd :: Proof -> Proof -> Proof
proofAnd = undefined

----------------------------------------------------------------
-- Proofs of formulas
----------------------------------------------------------------

type Sign = Bool

data ProofStep0
   = P0_True    Bool          -- ^  @[+True]@
   | P0_Assum   Formula          -- ^  @[+a, -a]@
   | P0_Hole    (Signed Formula) -- ^  Placeholder, fill in later
data ProofStep1
   = P1_Neg     (Signed Formula) -- !^  @G, {+/-}a@      ==>   @G, {-/+}~a@
   | P1_And     Formula Formula     -- !^  @G, a, b |- D@   ==>   @G, a&b |- D@
   | P1_BoxK    Agents        -- !^  @G |- D@         ==>   @K G |- K D@
   | P1_BoxT    Agents Formula   -- !^  @G, a |- D@      ==>   @G, K a |- D@
   | P1_Box4    Agents Formula   -- !^  @G |- K a, D@    ==>   @G |- K K a, D@
   | P1_Box5    Agents Formula   -- !^  @G |- ~K a, D@   ==>   @G |- K ~K a, D@
   | P1_CoHole  (Signed Formula) -- !^  Drop this term, fill in a proper proof later
data ProofStep2
   = P2_And     Formula Formula     -- ^  @G |- a, D@  and  @H |- b, E@  ==>  @G,H |- a&b, D,E@

data ProofTree
   = P0 ProofStep0
   | P1 ProofStep1 ProofTree
   | P2 ProofStep2 ProofTree ProofTree


type Sequent = Set (Signed Formula)

-- | Run a proof, return the resulting sequent
runProof :: ProofTree -> Sequent
runProof (P0 (P0_True t))      = Set.fromList [t +/- Truth t]
runProof (P0 (P0_Assum a))     = Set.fromList [Pos a, Neg a]
runProof (P1 (P1_Neg a) p)     = Set.insert (Neg Not <*> a) . Set.delete a                              $ runProof p
runProof (P1 (P1_And a b) p)   = Set.insert (Neg $ Bin And a b) . Set.delete (Neg a) . Set.delete (Neg b)   $ runProof p
runProof (P1 (P1_BoxK a) p)    = Set.map (fmap $ Box True a)                                               $ runProof p
runProof (P1 (P1_BoxT a t) p)  = Set.insert (Neg $ Box True a t) . Set.delete (Neg t)                      $ runProof p
runProof (P1 (P1_Box4 a t) p)  = Set.insert (Pos $ Box True a (Box True a t)) . Set.delete (Pos $ Box True a t)  $ runProof p
runProof (P2 (P2_And a b) p q) = Set.insert (Pos $ Bin And a b) $ Set.delete (Pos a) (runProof p) `Set.union` Set.delete (Pos b) (runProof q)

----------------------------------------------------------------
-- Combining proofs
----------------------------------------------------------------

joinProof :: ProofTree -> ProofTree -> ProofTree
joinProof = undefined

----------------------------------------------------------------
-- Proofs of formulas
----------------------------------------------------------------

{-
data Proof
   = ProofError  String
   | ProofFalsum              --  G,_|_  |-  a
   | ProofAssum  Formula         --  G,a |- a
   | ProofNeg    Bool Proof   --  G,a |- D  ==>  G,~a |- D  or vice versa
   | ProofAndA   Proof        --  G,a,b |- D  ==>  G,a&b |- D
   | ProofAndL   Proof        --  G,a |- D  ==>  G,a&b |- D
   | ProofAndR   Proof        --  G,a |- D  ==>  G,b&a |- D
   | ProofAndP   Proof Proof  --  G |- a,D  &&  H |- b,E  ==>  G,H |- a&b,D,E
   | ProofBox    Agent Proof  --  G |- D   ==>  K_i G |- K_i D
   | ProofSerial Agent Proof
   | ProofRefl   Agent Proof
 deriving (Show)
-}

data Proof
    = ProofTrue   HalfProof
    | ProofAssum  Formula HalfProof HalfProof
    | ProofAnd    Proof Proof
  deriving ()

instance Show Proof where
    show (ProofTrue       a) = "_|_:  " ++ show a 
    show (ProofAssum  t a b) = show t ++ " |-  " ++ show a ++ "\n" ++ show t ++ " -|  " ++ show b
    show (ProofAnd      a b) = "\nAND: " ++ indent (show a) ++ "AND: " ++ indent (show b)
      where indent = unlines . map ('\t':) . lines

instance Monoid Proof where
    mempty  = error "only use mappend"
    mappend = ProofAnd

{-
instance Error Proof where
   strMsg = ProofError
-}
