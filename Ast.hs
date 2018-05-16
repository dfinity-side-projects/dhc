{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
module Ast
  ( Ast(..)
  , AAst(..)
  , AstF(..)
  , deAnn
  , ffix
  , Type(..)
  ) where

import Data.Binary (Binary)
#ifndef __HASTE__
import Data.ByteString.Short (ShortByteString)
#endif
import Data.Int
import GHC.Generics (Generic)

#ifdef __HASTE__
type ShortByteString = String
#endif

instance Binary Type

infixl 5 :@
data AstF a = Qual String String
  | CallSlot [Type] [a]
  | Pack Int Int | I Int64 | S ShortByteString | Var String
  | a :@ a | Cas a [(a, a)]
  | Lam [String] a | Let [(String, a)] a
  | Placeholder String Type deriving (Read, Show, Functor, Foldable, Traversable, Generic)

newtype Ast = Ast (AstF Ast) deriving (Show, Generic)

-- Annotated AST.
data AAst a = AAst a (AstF (AAst a)) deriving (Show, Functor)

deAnn :: AAst a -> Ast
deAnn = ffix $ \h (AAst _ ast) -> Ast $ h ast

ffix :: Functor f => ((f a -> f b) -> a -> b) -> a -> b
ffix f = f $ fmap $ ffix f

infixr 5 :->
data Type = TC String | TApp Type Type | Type :-> Type
  | TV String | GV String deriving (Read, Show, Eq, Generic)
