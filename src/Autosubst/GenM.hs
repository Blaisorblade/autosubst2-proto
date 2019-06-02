{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Autosubst.GenM
  -- Signature reader monad
  ( SigM
  , runSig
  -- Generator monad
  , GenM
  , runGen
  -- Generating fresh names
  , fresh
  , tfresh
  , intern
  , Scope
  , withScope
  -- Accessing the signature
  , constructors
  , substOf
  , components
  , isOpen
  , arguments
  -- Producing output
  , write
  , hasArgs
  , definable
  , recursive
  ) where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.RWS
import           Data.Char               (toLower)
import qualified Data.Map                as M
import qualified Data.Set                as S
import           Text.PrettyPrint.Leijen hiding ((<$>))

import           Autosubst.Types

-- FIXME: Are we using an outdated PP library? Why isn't this defined?
instance Monoid Doc where
  mappend = (Text.PrettyPrint.Leijen.<>)
  mempty = empty

type Scope = M.Map Id Int

type SigM = ReaderT Signature (Except String)
type GenM = RWST Signature Doc Scope (Except String)

runSig :: Signature -> SigM a -> Either String a
runSig sig m = runExcept $ runReaderT m sig

runGen :: Signature -> GenM () -> Either String Doc
runGen sig m = runExcept $ snd <$> evalRWST m sig M.empty

-- Generating fresh names

lookupScope :: Id -> Scope -> Int
lookupScope = M.findWithDefault 0

fresh :: Id -> GenM Id
fresh id = do
  scope <- get
  let n = lookupScope id scope
  put $ M.insert id (n+1) scope
  if n > 0
    then return $ id ++ show n
    else return id

tfresh :: Id -> GenM Id
tfresh id = do
  scope <- get
  let n = lookupScope id scope
  if n > 0
    then return $ id ++ show n
    else return id

-- By default, use the first character of the type
intern :: TId -> GenM Id
intern (c:_) = fresh [toLower c]

withScope :: GenM a -> GenM a
withScope m = do
  scope <- get
  v <- m
  put scope
  return v

-- Accessing the signature
-- These functions work on both GenM and SigM

constructors :: (MonadReader Signature m, MonadError String m) => TId -> m [Constructor]
constructors id = do
  spec <- asks sigSpec;
  case M.lookup id spec of
    Just cs -> return cs
    Nothing -> throwError $ "constructors called on invalid type: " ++ id

substOf :: (MonadReader Signature m, MonadError String m) => TId -> m [TId]
substOf id = do
  substs <- asks sigSubstOf
  case M.lookup id substs of
    Just ts -> return ts
    Nothing -> throwError $ "substOf called on invalid type: " ++ id

components ::(MonadReader Signature m) => m [[TId]]
components = asks sigComponents

isOpen :: (MonadReader Signature m) => TId -> m Bool
isOpen id = S.member id <$> asks sigIsOpen

definable :: (MonadReader Signature m, MonadError String m) => TId -> m Bool
definable id = do
  b <- isOpen id
  cs <- constructors id
  return $  b || (not . null) cs

-- Yields true if at least one variable is contained.
hasArgs :: (MonadReader Signature m, MonadError String m) => TId -> m Bool
hasArgs id = fmap (not . null) (substOf id)

arguments :: (MonadReader Signature m, MonadError String m) => TId -> m [TId]
arguments id = do
  args <- asks sigArguments
  case M.lookup id args of
    Just ts -> return ts
    Nothing -> throwError $ "arguments called on invalid type: " ++ id

successors :: (MonadReader Signature m, MonadError String m) => TId -> m [TId]
successors id = do
  cs <- constructors id
  return $ concatMap (\(Constructor _ ps) -> concatMap (\(Position _ x) -> getIds x) ps) cs

-- Checks whether definitions will require recursive definitions.
-- This will be necessary later on, because Fixpoints don't reduce in the proper way in Coq, if there is no dedicated recursive argument.
recursive :: [TId] -> GenM Bool
recursive xs = do
  args <- successors (head xs)
  return $ (not . null) [x | x <- xs, x `elem` args]

-- Producing output

write :: Doc -> GenM ()
write = tell
