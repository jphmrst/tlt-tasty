{-|
Module      : TastyTLT
Description : Testing in a monad transformer layer
Copyright   : (c) John Maraist, 2022
License     : GPL3
Maintainer  : haskell-tlt@maraist.org
Stability   : experimental
Portability : POSIX

This module allows TLT tests to be named and called from within Tasty.
TLT is a small unit test system oriented towards examining
intermediate results of computations in monad transformers.  It is
intended to be lightweight for the programmer, and does not require
tests to be specified in some sort of formal list of tests.  Rather,
tests are simply commands in a monad stack which includes the
transformer layer @Test.TLT@.

See the @Test.TLT@ Haddock page or the GitHub repository
<https://github.com/jphmrst/TLT/> for more information out TLT.

-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- For Tasty
{-# LANGUAGE DeriveDataTypeable #-}

module Test.TastyTLT (tltTest) where

import Control.Monad.IO.Class
import Data.Typeable
import Test.TLT
import qualified Test.Tasty.Providers as TTP

-- * TLT integration

instance (Typeable m, MonadIO m) => TTP.IsTest (TLT m ()) where
  -- options :: Test.Tasty.Options.OptionSet, https://tinyurl.com/y5x2nenr
  run options tlt _ = error "TODO"

  -- testOptions :: Tagged (TLT m ()) [OptionDescription]
  testOptions = error "TODO"

tltTest :: String -> TLT IO () -> TTP.TestTree
tltTest = TTP.singleTest
