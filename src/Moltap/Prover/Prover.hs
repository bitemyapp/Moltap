
module Moltap.Prover.Prover
    ( proof
    ) where

import qualified Data.Map as Map
import Control.Monad
import Control.Applicative

import Data.List
import Moltap.Base.Syntax
import Moltap.Base.Agents
import Moltap.Base.Proof
import Moltap.Base.Model
import Moltap.Prover.TableauState

--------------------------------------------------------------------------------
-- High level interface
--------------------------------------------------------------------------------

-- | Proof a formula or find a counter model
proof :: Program -> Either Proof CounterModel
proof = uncurry proofFormula . evalProgram

-- | Proof a formula or find a counter model
proofFormula :: Axioms -> Formula -> Either Proof CounterModel
proofFormula ax f = case execSSM (emptyTableauState ax) (tableaux f (Pos [])) of
            Left  prf -> Left prf
            Right tab -> Right $ simplifyModel (|/= f)
                               $ axiomaticClosure (agents f) ax
                               $ mkCounterModel tab

--------------------------------------------------------------------------------
-- Universals and memoization
--------------------------------------------------------------------------------

type TableauState = GenTableauState HalfProof Proof
type TableauM     = GenTableauM_    HalfProof Proof

exhausted :: TableauM
exhausted = return ()

-- | Add the given signed term to the tableau, and continue reasoning
tableaux :: Formula -> HalfProof -> TableauM
tableaux = tabMemo (\t p1 p -> if sign p1 == sign p
                               then exhausted
                               else abort $ ProofAssum t p1 p)
                   tableaux'

-- | Add a necessitiy
necessity :: Agents -> Formula -> HalfProof -> TableauM
necessity a f p = tabAddUniv a (tableaux f p)

--------------------------------------------------------------------------------
-- Recursion over formulas
--------------------------------------------------------------------------------

tableaux' :: Formula -> HalfProof -> TableauM

tableaux' (Truth     t) sp
    | sign sp == t             = abort $ ProofTrue sp
    | otherwise                = exhausted

-- in general, there is nothing we can say about variables
tableaux' (Var       _) _      = exhausted

-- for not: flip the sign
tableaux' (Not       a) sp     = tableaux a $ (HProofNeg (sign sp) a:) <$> flipSign sp

-- equivalence
tableaux' (Bin o a b) sp
    -- to proof "a <-> b +", proof "~a or b  and  a or ~b
    | sign sp == signOuter && isEquiv
                               = split (do tableaux a $ flipSign sp
                                           tableaux b $ sp)
                                       (do tableaux a $ sp
                                           tableaux b $ flipSign sp)
    -- to proof "a != b +", proof "a or b  and  ~a or ~b"
    | isEquiv                  = split (do tableaux a $ sp
                                           tableaux b $ sp)
                                       (do tableaux a $ flipSign sp
                                           tableaux b $ flipSign sp)
    -- to proof "a & b +", we have to proof both
    | sign sp == signOuter     = split (tableaux a $ (HProofSplitL b:) <$> signL sp)
                                       (tableaux b $ (HProofSplitR b:) <$> signR sp)
    -- to proof "a & b -", we have to proof either one
    | otherwise                = do    (tableaux a $ (HProofAndL   b:) <$> signL sp)
                                       (tableaux b $ (HProofAndR   b:) <$> signR sp)
  where (isEquiv,signOuter,signL,signR) = operatorSign o

-- box/diamond
tableaux' f@(Box  s a t) sp
    | sign sp == s             = tabLocalUpIf ax4 a (tableaux f sp)
                               $ tabLocalDown a -- it is a goal, skolem
                               $ tableaux t ((HProofBoxN a t:) <$> sp)
    | otherwise                = do tabWhenAxiom (\x -> axD x && not (axT x)) a $
                                      tableaux (Box (not s) a t) sp
                                    tabLocalUpIf ax5 a (tableaux f sp) $ do
                                      necessity a t ((HProofBoxJ a t:) <$> sp)
                                      tabWhenAxiom axT a $
                                         tableaux t ((HProofBoxP a t:) <$> sp) -- K a -> a, a -> M a

-- common knowledge
tableaux' f@(Star s a t) sp     
    | sign sp == s             = error "Can't prove common knowledge yet"
    | otherwise                = tabLocalUpIf ax5 a (tableaux f sp)
                               $ do let rec = (tableaux t sp >> tabAddUniv a rec)
                                    tabAddUniv a rec
                                    rec

-- ignore notes
tableaux' (Note _ f) sp        = tableaux' f sp


-- | Information on operators
--
--   > 1. is it an equivalence operator == or /=
--   > 2. is it a conjunction / positive equivalence
--   > 3. how to flip the sign for the left/right part
operatorSign :: BinOp -> (Bool, Bool, Signed a -> Signed a, Signed a -> Signed a)
operatorSign And    = (False, True,  id,       id)
operatorSign Or     = (False, False, id,       id)
operatorSign Imp    = (False, False, flipSign, id)
operatorSign Pmi    = (False, False, id, flipSign)
operatorSign Equiv  = (True,  True,  undefined, undefined)
operatorSign Differ = (True,  False, undefined, undefined)

--------------------------------------------------------------------------------
-- Countermodels
--------------------------------------------------------------------------------

type CounterModel = Model Int

-- | Make a counter model representing a tableaux state
mkCounterModel :: TableauState -> CounterModel
mkCounterModel tb = Model
    { modValuation = Map.fromList
                     [ (l,vars)
                     | (l,tab,_) <- graph
                     , let vars = Map.fromList [ (v, not $ sign p) | (Var v, p) <- Map.toList $ tabSeen tab ]
                     ]
    , modRelations = Map.fromListWith (Map.unionWith (++))
                     [ (a, Map.singleton l1 [l2])
                     | (l1,_,links) <- graph
                     , (l2,a) <- links
                     ]
    , modRoot      = 0
    }
  where graph = tabGraph tb
