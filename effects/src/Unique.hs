
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- |
-- Module      :  Unique
-- Copyright   :  (c) Iago Abal 2011-2012
-- License     :  BSD3
--
-- Maintainer  :  Iago Abal, iago.abal@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Uniques generation.

module Unique
  ( Uniq
  , Uniquable(..)
  , UniqSupply, mkSupply, newSupply, next, split
  , MonadUnique(..)
  , UniqueT(..), evalUniqueT, runUniqueT
  , Unique(..), evalUnique, runUnique
  )
  where


import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State.Strict ( StateT, runStateT, evalStateT )
import qualified Control.Monad.State.Strict as ST
import Control.Monad.Trans.Maybe

import Data.Data ( Data, Typeable )


type Uniq = Int


-- | Types whose inhabitants are uniquely identified.
class Uniquable a where
  uniqOf :: a -> Uniq


-- * Unique supply

data UniqSupply = UniqSupply { _inc :: !Int, _first :: !Uniq }
  deriving (Eq,Typeable,Data)

mkSupply :: Uniq -> UniqSupply
mkSupply = UniqSupply 1

newSupply :: UniqSupply
newSupply = mkSupply 0

next :: UniqSupply -> (Uniq,UniqSupply)
next (UniqSupply inc x) = (x,UniqSupply inc (x+inc))

split :: UniqSupply -> (UniqSupply,UniqSupply)
split (UniqSupply i x) = (UniqSupply (2*i) x, UniqSupply (2*i) (x+1))


-- * MonadUnique
-- A monad to supply unique values.

class Monad m => MonadUnique m where
  getUniq :: m Uniq
  forkSupply :: m UniqSupply

instance MonadUnique m => MonadUnique (ReaderT r m) where
  getUniq = lift getUniq
  forkSupply =  lift forkSupply

instance MonadUnique m => MonadUnique (MaybeT m) where
  getUniq = lift getUniq
  forkSupply =  lift forkSupply

-- * UniqueT monad transformer

newtype UniqueT m a = UniqueT { unUniqueT :: StateT UniqSupply m a }
  deriving(Functor, Monad, MonadTrans, MonadIO)

evalUniqueT :: Monad m => UniqueT m a -> UniqSupply -> m a
evalUniqueT = evalStateT . unUniqueT

runUniqueT :: Monad m => UniqueT m a -> UniqSupply -> m (a, UniqSupply)
runUniqueT = runStateT . unUniqueT


instance Monad m => MonadUnique (UniqueT m) where
    getUniq = UniqueT $ do
      (uniq,us') <- ST.gets next
      ST.put us'
      return uniq
    forkSupply = UniqueT $ do
      us <- ST.get
      let (us1,us2) = split us
      ST.put us1
      return us2

-- * Unique monad

newtype Unique a = Unique { unUnique :: UniqueT Identity a }
    deriving (Functor, Monad, MonadUnique)

evalUnique :: Unique a -> UniqSupply -> a
evalUnique m s =  runIdentity $ evalUniqueT (unUnique m) s

runUnique :: Unique a -> UniqSupply -> (a,UniqSupply)
runUnique m s =  runIdentity $ runUniqueT (unUnique m) s
