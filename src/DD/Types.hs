{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
---------------------------------------------------------------------
-- |
-- Module      :   CDCL.Types
-- Description :   Contains type declaration for CDCL Package
-- Copyright   :   (c) Andreas Hager, 2022
-- License     :   Apache-2.0
-- Maintainer  :
-- Stability   :
-- Portability :
--
---------------------------------------------------------------------
module DD.Types where

import           Data.Set (Set)
import qualified Data.Set as Set

import qualified Debug.Trace as D

-- | Result of DD algorithm
data DDResult = SAT [Var]
              | UNSAT
    deriving (Show, Eq, Ord)

---------------------------------------------------------------------
-- | Tree Datastructure for DD algorithm
--   CNF's are the leafes 
--   Term Int Term Term represents the disjuntion for the Variable Integer
data Term = UNSAT_LEAF
          | Leaf CNF
          | Node CNF Var Term Term -- First Term consists of clauses independent of Integer (memory consumption reduction)
          | Sol [Var]
    deriving (Show, Eq, Ord)

parseTerm :: [[Integer]] -> Term
parseTerm list = Leaf cnf
    where cnf = parseCNF list

getNextVar :: Term -> Var
getNextVar (Leaf cnf) = if Set.size cnf > 0 
            then let
                    firstClause = Set.elemAt 0 cnf 
                in (if Set.size firstClause > 0
                    then Set.elemAt 0 firstClause
                    else -1)
            else -1
getNextVar term@(Node _ _ left right) = if leftVar > -1 
    then leftVar
    else rightVar 
    where
        leftVar = getNextVar left
        rightVar = getNextVar right
getNextVar term = error ("Expected unsolved Term, but got: " ++ show term)

buildNextTerm :: Term -> Var -> Term
buildNextTerm term var = reduceFP newTerm
    where 
        negVar = setPolarity var Neg
        posVar = setPolarity var Pos
        negTerm = setVar term negVar
        posTerm = setVar term posVar
        newTerm = Node Set.empty posVar negTerm posTerm

setVar :: Term -> Var -> Term
setVar (Leaf cnf) var = Leaf result
    where 
        filteredCNF = Set.filter (\clause -> not (containsVar var clause)) cnf
        negatedVar = DD.Types.negate var
        result = Set.map (removeVar negatedVar) filteredCNF
setVar (Node common v left right) var = Node common' v left' right'
    where 
        (Leaf common') = setVar (Leaf common) var
        left' = setVar left var
        right' = setVar right var
setVar t _ = t

reduceFP :: Term -> Term
reduceFP term = if term == res
    then res
    else reduceFP res
    where res = reduce term 

reduce :: Term -> Term
reduce term@(Leaf cnf) = if isCNFUnfullfillable cnf 
    then UNSAT_LEAF 
    else term
reduce (Node _ _ UNSAT_LEAF UNSAT_LEAF) = UNSAT_LEAF

reduce (Node cnf v (Sol s) _) = if isCNFFullfilled cnf 
    then Sol s 
    else Node cnf v (Sol s) (Sol s)
reduce (Node cnf v _ (Sol s)) = if isCNFFullfilled cnf 
    then Sol s 
    else Node cnf v (Sol s) (Sol s)

reduce (Node cnf v (Node leftCNF vl ll rl) (Leaf rightCNF)) = Node cnf'' v (Node leftCNF' vl ll rl) (Leaf rightCNF')
    where 
        common = getCommon leftCNF rightCNF
        cnf' = Set.union cnf common
        (Leaf cnf'') = reduce (Leaf cnf')
        leftCNF' = removeClauses leftCNF common
        rightCNF' = removeClauses rightCNF common
reduce (Node cnf v (Leaf leftCNF) (Node rightCNF vr lr rr)) = Node cnf'' v (Leaf leftCNF') (Node rightCNF' vr lr rr)
    where 
        common = getCommon leftCNF rightCNF
        cnf' = Set.union cnf common
        (Leaf cnf'') = reduce (Leaf cnf')
        leftCNF' = removeClauses leftCNF common
        rightCNF' = removeClauses rightCNF common
reduce (Node cnf v (Node leftCNF vl ll rl) (Node rightCNF vr lr rr)) = Node cnf'' v (Node leftCNF' vl ll rl) (Node rightCNF' vr lr rr)
    where 
        common = getCommon leftCNF rightCNF
        cnf' = Set.union cnf common
        (Leaf cnf'') = reduce (Leaf cnf')
        leftCNF' = removeClauses leftCNF common
        rightCNF' = removeClauses rightCNF common


reduce (Node cnf var (Leaf left) (Leaf right))
    | Set.null cnf && (Set.null left || Set.null right) = Sol [var]
    | Set.null left || Set.null right                   = Node cnf var (Leaf Set.empty) (Leaf Set.empty)
    | otherwise                                         = Node cnf' var (Leaf leftCNF') (Leaf rightCNF')
        where 
            common = getCommon left right
            cnf' = Set.union cnf common
            leftCNF' = removeClauses left common
            rightCNF' = removeClauses right common

reduce node@(Node cnf var (Leaf left) right)
    | Set.null cnf && Set.null left = Sol [var]
    | Set.null left                 = Node cnf var (Leaf Set.empty) (Leaf Set.empty)
    | otherwise                     = node

reduce node@(Node cnf var left (Leaf right))
    | Set.null cnf && Set.null right = Sol [var]
    | Set.null right                 = Node cnf var (Leaf Set.empty) (Leaf Set.empty)
    | otherwise                      = node

reduce t = t

isSolved :: Term -> Bool
isSolved UNSAT_LEAF = False
isSolved (Sol _) = True
isSolved (Leaf cnf) = isCNFFullfilled cnf
isSolved (Node common _ left right) = isCNFFullfilled common 
    && (isSolved left || isSolved right)

isUnfullfillable :: Term -> Bool
isUnfullfillable UNSAT_LEAF = True
isUnfullfillable (Sol _) = False
isUnfullfillable (Leaf cnf) = isCNFUnfullfillable cnf
isUnfullfillable (Node common _ left right) = isCNFUnfullfillable common 
    || (isUnfullfillable left && isUnfullfillable right)

getSolution :: Term -> DDResult
getSolution (Sol solution) = SAT solution
getSolution (Leaf cnf) = if isCNFFullfilled cnf then SAT [] else UNSAT
getSolution (Node common var left right) = if isCNFFullfilled common
    then 
        let 
            leftSol = getSolution left
            rightSol = getSolution right
        in case (leftSol, rightSol) of
            (SAT sl, SAT sr) -> SAT (var:(sl ++ sr))
            (SAT l, _)       -> SAT ((-var):l)
            (_, SAT r)       -> SAT (var:r)
            (UNSAT, UNSAT)   -> UNSAT
    else UNSAT
---------------------------------------------------------------------
-- | A representation for a cnf as a set of clause
type CNF = Set.Set Clause

parseCNF :: [[Integer]] -> CNF
parseCNF list = cnf
    where 
        clauseList = map parseClause list
        cnf = Set.fromList clauseList

-- split :: CNF -> Var -> (CNF, CNF, CNF)
-- split cnf var = (common, pos, neg)
--     where
--         posVar = setPolarity var Pos
--         (negCNF, pos) = Set.partition (containsVar posVar) cnf
--         negVar = setPolarity var Neg
--         (common, neg) = Set.partition (containsVar negVar) negCNF

getCommon :: CNF -> CNF -> CNF
getCommon = Set.intersection

-- containsClause :: Clause -> CNF -> Bool
-- containsClause = Set.member

removeClauses :: CNF -> CNF -> CNF
removeClauses = Set.difference

--removeClause :: Clause -> CNF  -> CNF
--removeClause = Set.delete

isCNFFullfilled :: CNF -> Bool 
isCNFFullfilled = Set.null

isCNFUnfullfillable :: CNF -> Bool 
isCNFUnfullfillable = Set.member Set.empty

---------------------------------------------------------------------
-- | A Clause represented as a set of Integers
type Clause = Set.Set Var

parseClause :: [Integer] -> Clause
parseClause = Set.fromList

containsVar :: Var -> Clause -> Bool
containsVar = Set.member

removeVar :: Var -> Clause -> Clause
removeVar = Set.delete

isClauseUnfullfillable :: Clause -> Bool 
isClauseUnfullfillable = Set.null

---------------------------------------------------------------------
type Var = Integer

setPolarity :: Var -> Polarity -> Var
setPolarity var pol = polarityToSign pol * abs var

negate :: Var -> Var
negate var = -1 * var

getPolarity :: Var -> Polarity
getPolarity var = if var >= 0 then Pos else Neg

data Polarity = Pos | Neg
    deriving (Show, Eq, Ord)

polarityToSign :: Polarity -> Integer
polarityToSign Pos = 1
polarityToSign Neg = -1
