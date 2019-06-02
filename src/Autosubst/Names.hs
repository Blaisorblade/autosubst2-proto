{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Autosubst.Names where

import           Autosubst.GenM
import           Autosubst.Syntax
import           Autosubst.Types
import           Data.List        as L

-- Contains the names of the later functions / inductive datatypes etc.

-- TODO: Sort.

-- Separation symbol
sep :: String
sep = "_"

-- Variable constructors
var_ :: TId -> String
var_ x = "var" ++ sep ++ x

constructor_ :: TId -> String
constructor_ c = c

-- Name for toVarRen functions
toVarRen_ :: TId -> String
toVarRen_ x = "toVarRen" ++ sep ++ x

-- Name of types for renaming/substitutions
renTy_ :: TId -> String
renTy_ x = "renTy" ++ sep ++ x

substTy_ :: TId -> String
substTy_ x = "substTy" ++ sep ++ x

ren_ :: TId -> String
ren_ x = "ren" ++ sep ++ x

-- Name for Casts
castRen_ :: TId -> TId -> String
castRen_ x y = "castRen" ++ sep ++ x ++ sep ++ y

-- Up Functions
upRen_ :: TId -> TId -> String
upRen_ x y = "upRen" ++ sep ++ x ++ sep ++ y

-- Definition of Substitution
cast_ :: TId -> TId -> String
cast_ x y = "cast" ++ sep ++ x ++ sep ++ y

toVar_ :: TId -> String
toVar_ x = "toVar" ++ sep ++ x

up_ ::  TId -> TId -> String
up_ x y = "up" ++ sep ++ x ++ sep ++ y

subst_ :: TId -> String
subst_ x = "subst" ++ sep ++ x

substtc_ :: TId -> String
substtc_ x = "Subst" ++ sep ++ x

rentc_ :: TId -> String
rentc_ x = "Ren" ++ sep ++ x

vartc_ :: TId -> String
vartc_ x = "VarInstance" ++ sep ++ x


-- Name for predicate that two substitutions are eequivalent
eqRen_ :: TId -> String
eqRen_ x = "eqRen" ++ sep ++ x

eqSubst_ :: TId -> String
eqSubst_ x = "eqSubst" ++ sep ++ x

-- Lifting from x to y on component z
upId_ :: TId -> TId -> String
upId_ x y = "upId" ++ sep ++ x ++ sep ++ y

idSubst_ :: TId -> String
idSubst_ x = "idSubst" ++ sep ++ x

congr_ :: TId -> String
congr_ c = "congr" ++ sep ++ c

up_ren_ren_ :: String
up_ren_ren_ = "up_ren_ren"

up_ren_subst_ :: TId -> TId -> String
up_ren_subst_ x y = "up_ren_subst" ++ sep ++ x ++ sep ++ y

up_subst_ren_ :: TId -> TId -> String
up_subst_ren_ x y = "up_subst_ren" ++ sep ++ x ++ sep ++ y

up_subst_subst_ :: TId -> TId -> String
up_subst_subst_ x y = "up_subst_subst" ++ sep ++ x ++ sep ++ y

rinstInst_ :: TId -> String
rinstInst_ x = "rinst_inst" ++ sep ++ x

up_rinstInst_ :: TId -> TId -> String
up_rinstInst_ x y = "rinstInst_up" ++ sep ++ x ++ sep ++ y

upExtRen_ :: TId -> TId -> String
upExtRen_ x y = "upExtRen" ++ sep ++ x ++ sep ++ y

upExt_ :: TId -> TId -> String
upExt_ x y = "upExt" ++ sep ++ x ++ sep ++ y

ext_ :: TId -> String
ext_ x = "ext" ++ sep ++ x

extRen_ :: TId -> String
extRen_ x = "extRen" ++ sep ++ x

compRenRen_ :: TId -> String
compRenRen_ x = "compRenRen" ++ sep ++ x

compRenSubst_ :: TId -> String
compRenSubst_ x = "compRenSubst" ++ sep ++ x

compSubstRen_ :: TId -> String
compSubstRen_ x = "compSubstRen" ++ sep ++ x

compSubstSubst_ :: TId -> String
compSubstSubst_ x = "compSubstSubst" ++ sep ++ x

lidComp_ :: TId -> String
lidComp_ x = "lidComp" ++ sep ++ x
