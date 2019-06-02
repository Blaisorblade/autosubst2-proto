{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Autosubst.GenCode (generateCode) where

import           Autosubst.Generator
import           Autosubst.Types
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.RWS       hiding ((<>))

import           Autosubst.GenM
import qualified Data.Map                as M
import           Data.Maybe              as Maybe
import           Prelude                 hiding ((<$>))
import           Text.PrettyPrint.Leijen

import           Autosubst.Automation
import           Autosubst.Signature
import           Autosubst.Syntax
import           Data.List               as L

import           Autosubst.Agda
import           Autosubst.Coq
import           Autosubst.Lean
import           Autosubst.UCoq


genCode :: [[TId]] -> GenM [Sentence]
genCode xs = do
  let all = [(x,y) | x <- concat xs, y <- concat xs] -- get all up-pairs
--  xs <- filterM (\y -> fmap (not . null) (substOf (head y))) xs -- Filter xs to contain only those which have variables.
  (_, code) <- foldM (\(ups,sentences) x -> do
                                  xs <- substOf (L.head x)
                                  let up_x = [(x, y) | x <- xs, y <- xs]
                                  code_x <- genCodeT x (L.filter (`elem` ups) up_x)
                                  return (L.filter (`notElem` up_x) ups, sentences ++ [code_x]))
                                  (all, []) xs
  return $ concat code

-- Embedding in the monadic structure
generateCode :: Prover -> GenM ()
generateCode p = do
  spec <- components
  code <- genCode spec
  varSorts <- filterM isOpen (concat spec)
  substSorts <- filterM (\x -> do
                               xs <- substOf x
                               return $ not $ null xs) (concat spec)
  ups <- mapM (\x -> do
                     xs <- substOf (L.head x)
                     return [(x,y) | x <- xs, y <- xs]) spec
  auto <- genAutomation varSorts (concat spec) substSorts (nub (concat ups))
  case p of Coq -> tell (coqPreamble <$$> empty <$$> vsep (map (\s -> coqShow s <$$> empty) (code ++ auto)))
            UCoq -> tell (ucoqPreamble <$$> empty <$$> vsep (map (\s -> ucoqShow s <$$> empty) (code ++ auto)))
            Lean -> tell (leanPreamble <$$> empty <$$> vsep (map (\s -> leanShow s <$$> empty) (code ++ auto)))
            Agda -> tell (agdaPreamble <$$> empty <$$> vsep (map (\s -> agdaShow s <$$> empty) (code ++ auto)))
  return ()
