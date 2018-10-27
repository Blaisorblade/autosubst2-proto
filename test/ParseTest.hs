module ParseTest where

import qualified Data.Map as M
import Autosubst.Parser
import Autosubst.Types

-- Errors

doubleDefinition :: String
doubleDefinition = "x : type\n\
                   \x : type"

doubleConstructor :: String
doubleConstructor = "x : type\n\
                    \c : x\n\
                    \c : x -> x"

keywordType :: String
keywordType = "Definition : type"

keywordConstructor :: String
keywordConstructor = "x : Type\n\
                     \where : (x -> x) -> x"

thirdOrderConstructor :: String
thirdOrderConstructor = "tm  : Type\n\
                        \nam : Type\n\
                        \mu  : ((tm -> nam) -> nam) -> tm"

unknownType :: String
unknownType = "c : tp"

-- Input example

untypedLambdaInput :: String
untypedLambdaInput = "tm : Type\n\
                     \app : tm -> tm -> tm\n\
                     \lam : (tm -> tm) -> tm\n"

untypedLambdaSpec :: Spec
untypedLambdaSpec = M.fromList
  [ ("tm", [appConstructor, lamConstructor]) ]
  where appConstructor = Constructor "app" [tmPosition, tmPosition]
        lamConstructor = Constructor "lam" [absPosition]
        tmPosition = Position [] "tm"
        absPosition = Position ["tm"] "tm"
