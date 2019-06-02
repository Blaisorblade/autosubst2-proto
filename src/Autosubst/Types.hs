module Autosubst.Types
  ( Id
  , Typevar
  , TId
  , CId
  , FId
  , Spec
  , Constructor(..)
  , Position(..)
  , Binder
  , Argument(..)
  , getIds
  , Signature(..)
  , Prover (..)
  ) where

import qualified Data.Map as M
import qualified Data.Set as S

-- Provers
data Prover = Coq | UCoq | Lean | Agda deriving (Show, Read)

-- identifiers
type Id = String
type Typevar = String
type TId = Id
type CId = Id
type FId = Id

-- specifications -- TODO: nicer instance for Show, default is ugly as heck

type Spec = M.Map TId [Constructor]

data Constructor = Constructor
  { name      :: CId
  , positions :: [Position]
  } deriving (Show)

data Position = Position
  { binders  :: [Binder]
  , argument :: Argument
  } deriving (Eq, Show)

type Binder = TId
data Argument = Atom TId | FunApp FId [Argument] deriving (Eq, Show)

-- TODO: Does not fit here.
getIds :: Argument -> [TId]
getIds (Atom x)      = [x]
getIds (FunApp _ xs) = concat (map getIds xs)

-- signatures -- TODO: same as above, show on signature looks messy

data Signature = Signature
  { sigSpec       :: Spec
  , sigSubstOf    :: M.Map TId [TId]
  , sigComponents :: [[TId]]
  , sigIsOpen     :: S.Set TId
  , sigArguments  :: M.Map TId [TId]
  } deriving (Show)
