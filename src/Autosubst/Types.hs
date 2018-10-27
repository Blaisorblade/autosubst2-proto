module Autosubst.Types
  ( Id
  , TId
  , CId
  , Spec
  , Constructor(..)
  , Position(..)
  , Binder
  , Argument
  , Signature(..)
  ) where

import qualified Data.Map as M
import qualified Data.Set as S

-- identifiers

type Id = String
type TId = Id
type CId = Id

-- specifications -- TODO: nicer instance for Show, default is ugly as heck

type Spec = M.Map TId [Constructor]

data Constructor = Constructor
  { name      :: CId
  , positions :: [Position]
  } deriving (Show)

data Position = Position
  { binders  :: [Binder]
  , argument :: Argument
  } deriving (Show)

type Binder = TId
type Argument = TId

-- signatures -- TODO: same as above, show on signature looks messy

data Signature = Signature
  { sigSpec :: Spec
  , sigSubstOf :: M.Map TId [TId]
  , sigComponents :: [[TId]]
  , sigIsOpen :: S.Set TId
  , sigArguments :: M.Map TId [TId]
  } deriving (Show)
