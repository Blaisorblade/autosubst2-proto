-- QuickCheck generator for specifications
-- This is supposed to be used for fuzzing the code generator, e.g.,
-- we generate a random spec, generate coq code for it and check that
-- coq can typecheck the generated file.
-- TODO: cleanup
module GenSpec where

import           Control.Monad
import qualified Data.Map        as M
import           Test.QuickCheck

import           Parser
import           Typecheck

-- Generate arbitrary well-formed specs

genId :: Gen Id
genId = liftM2 (:) (elements alpha) (listOf $ elements alnum)
  where alpha = ['a' .. 'z'] ++ ['A' .. 'Z']
        alnum = alpha ++ ['0' .. '1'] ++ ['_']

genFresh :: [Id] -> Gen Id
genFresh ids = do id <- genId; if id `elem` ids then genFresh ids else return id

genTypes :: Gen [TId]
genTypes = sized (go [])
  where go tps 0 = return tps
        go tps n = do tp <- genFresh tps; go (tp:tps) (n-1)

genConstructor :: [TId] -> [CId] -> Gen Constructor
genConstructor tps cs = liftM2 Constructor name $ listOf position
  where name     = genFresh $ tps ++ cs
        position = liftM2 Position (listOf tp) tp
        tp       = elements tps

genConstructors :: [TId] -> [CId] -> Gen [Constructor]
genConstructors tps cs = sized $ go cs
  where go cs 0 = return []
        go cs n = do
          c  <- genConstructor tps cs
          cr <- go (name c : cs) (n-1)
          return (c:cr)

genSpecFor :: [TId] -> [CId] -> Spec -> TId -> Gen ([CId], Spec)
genSpecFor tps cs spec tp = do
  constructors <- genConstructors tps cs
  return (map name constructors, M.insert tp constructors spec)

genSpec :: Gen Spec
genSpec = do
  tps <- genTypes
  snd <$> foldM (\(cs, spec) tp -> genSpecFor tps cs spec tp) ([], M.empty) tps

-- FIXME: Don't use a type synonym for Spec
data SPEC = SPEC Spec

instance Arbitrary SPEC where
  arbitrary = SPEC <$> genSpec
