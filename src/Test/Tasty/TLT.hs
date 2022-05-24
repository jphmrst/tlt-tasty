{-|
Module      : TLT
Description : Calling TLT tests from Tasty
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

-}

{-# LANGUAGE FlexibleInstances #-}

module Test.Tasty.TLT (tltTest) where

import Control.Monad.IO.Class
import Data.Typeable
import Data.Tagged
import Test.TLT.Results (formatFail, totalFailCount)
import Test.TLT.Class
import qualified Test.Tasty.Providers as TTP

-- * TLT integration

class MonadIO m => TastyTLT m where runOuter :: m a -> IO a
instance TastyTLT IO where runOuter = id

instance (Typeable m, TastyTLT m) => TTP.IsTest (TLT m ()) where
  -- options :: Test.Tasty.Options.OptionSet, https://tinyurl.com/y5x2nenr
  run options tlt _ = do
    (optsOut, results) <- runOuter $ runTLT tlt
    return $ case totalFailCount results of
      0 -> TTP.testPassed ""
      _ -> TTP.testFailed
             (show (length results) ++ " errors found in TLT invocation")

  testOptions = return []

tltTest :: String -> TLT IO () -> TTP.TestTree
tltTest = TTP.singleTest
