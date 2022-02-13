{-|
Module      : TLT
Description : Testing in a monad transformer layer
Copyright   : (c) John Maraist, 2022
License     : GPL3
Maintainer  : haskell-tlt@maraist.org
Stability   : experimental
Portability : POSIX

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
implied, for NON-COMMERCIAL use.  See the License for the specific
language governing permissions and limitations under the License.

-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.TLT (
  -- * A monad transformer for housing a test process
  TLT, tlt, -- MonadTLT,
  -- * Writing tests
  Assertion,
  -- ** `TLT` commands
  inGroup, (~:), (~::), (~::-),
  -- ** Assertions
  (!==),  (!/=),  (!<),  (!>),  (!<=),  (!>=),
  (!==-), (!/=-), (!<-), (!>-), (!<=-), (!>=-),
  empty, nonempty, nothing, emptyP, nonemptyP, nothingP,
  -- ** Building new assertions
  liftAssertion2Pure, assertion2PtoM, liftAssertion2M,
  liftAssertionPure, assertionPtoM, liftAssertionM

  -- * Examples

  -- |A simple example with vacuous tests:
  --
  -- > main :: IO ()
  -- > main = do
  -- >   tlt test
  -- >
  -- > test :: Monad m => TLT m ()
  -- > test = do
  -- >   "True passes" ~::- True
  -- >   "2 is 3 as single Bool" ~::- 2 == 3
  -- >   "2 is 2 as single Bool" ~::- 2 == 2
  -- >   inGroup "== assertions" $ do
  -- >     inGroup "pure" $ do
  -- >       "2 is 3 as pure assertion" ~: 2 !==- 3
  -- >       "2 is 2 as pure assertion" ~: 2 !==- 2
  -- >     inGroup "monadic" $ do
  -- >       "2 is 3 as result" ~: 2 !== return 3
  -- >       "2 is 2 as result" ~: 2 !== return 2
  -- >   inGroup "/= pure assertions" $ do
  -- >     "2 not 3" ~: 2 !/=- 3
  -- >     "2 not 2" ~: 2 !/=- 2
  -- >   "2 not 3 as result" ~: 2 !/= return 3
  -- >   "2 not 2 as result" ~: 2 !/= return 2
  --
  -- Running these tests should give:
  --
  -- > Running tests:
  -- > - True passes: Pass
  -- > - 2 is 3 as single Bool: FAIL Expected True but got False
  -- > - 2 is 2 as single Bool: Pass
  -- > - == assertions:
  -- >   - pure:
  -- >     - 2 is 3 as pure assertion: FAIL Expected 2 but got 3
  -- >     - 2 is 2 as pure assertion: Pass
  -- >   - monadic:
  -- >     - 2 is 3 as result: FAIL Expected 2 but got 3
  -- >     - 2 is 2 as result: Pass
  -- > - /= pure assertions:
  -- >   - 2 not 3: Pass
  -- >   - 2 not 2: FAIL Expected other than 2 but got 2
  -- > - 2 not 3 as result: Pass
  -- > - 2 not 2 as result: FAIL Expected other than 2 but got 2
  -- > Found 5 errors in 11 tests; exiting

  ) where

import Data.Maybe
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import System.Console.ANSI
import System.Exit

-- * Results of tests

-- |Reasons why a test might fail
data TestFail = Asserted String | Erred

formatFail :: TestFail -> String
formatFail (Asserted s) = s
formatFail (Erred) = "Assertion called error"

-- |An assertion is a computation (typically in the monad wrapped by
-- `TLT`) which returns a list of zero of more reasons for the failure
-- of the assertion.  A successful computation returns an empty list:
-- no reasons for failure, hence success.
type Assertion m = m [TestFail]

-- |Hierarchical structure holding the result of running tests,
-- possibly grouped into tests.
data TestResult = Test String [TestFail]
                | Group String Int Int [TestResult]
                  -- Ints are resp. total tests, failures

-- |Return the number of failed tests reported in a `TestResult`.
failCount :: TestResult -> Int
failCount (Test _ []) = 0
failCount (Test _ _) = 1
failCount (Group _ _ n _) = n

testCount :: TestResult -> Int
testCount (Test _ _) = 1
testCount (Group _ n _ _) = n

totalFailCount :: [TestResult] -> Int
totalFailCount = foldr (+) 0 . map failCount

totalTestCount :: [TestResult] -> Int
totalTestCount = foldr (+) 0 . map testCount

-- |Report the results of tests.
report :: TLTopts -> [TestResult] -> IO ()
report opts trs = let fails = totalFailCount trs
                      tests = totalTestCount trs
                  in do report' "" trs
                        if fails > 0
                          then do putStrLn $
                                    "Found " ++ show fails ++ " error"
                                    ++ (if fails > 1 then "s" else "")
                                    ++ " in " ++ show tests ++ " tests; exiting"
                                  exitFailure
                          else putStrLn $ show tests ++ " test"
                               ++ (if tests > 1 then "s" else "")
                               ++ " passing."
  where report' ind trs = forM_ trs $ \ tr -> do
          case tr of
            Test s r -> do
              putStr $ ind ++ "- " ++ s ++ ": "
              case r of
                [] -> do
                  greenPass
                  putStrLn ""
                x : [] -> do
                  redFail
                  putStrLn $ " " ++ formatFail x
                _ -> do
                  redFail
                  putStrLn ":"
                  forM_ r $ \ f -> putStrLn $ ind ++ "- " ++ formatFail f
            Group s _ _ trs' -> do
              putStrLn $ ind ++ "- " ++ s ++ ":"
              report' ("  " ++ ind) trs'

greenPass = do
  setSGR [
    SetColor Foreground Vivid Blue
    ]
  putStr "Pass"
  setSGR [
    SetColor Foreground Vivid Black
    ]

redFail = do
  setSGR [
    SetColor Foreground Vivid Red,
    SetConsoleIntensity BoldIntensity
    ]
  putStr "FAIL"
  setSGR [
    SetColor Foreground Vivid Black,
    SetConsoleIntensity NormalIntensity
    ]

-- |Accumulator for test results, in the style of a simplified Huet's
-- zipper which only ever adds to the end of the structure.
data TRBuf = Buf TRBuf Int Int String [TestResult] | Top Int Int [TestResult]

-- |Add a single test result to a `TRBuf`.
addResult :: TRBuf -> TestResult -> TRBuf
addResult (Top tc fc trs) tr =
  Top (tc + testCount tr) (fc + failCount tr) $ tr : trs
addResult (Buf up tc fc s trs) tr =
  Buf up (tc + testCount tr) (fc + failCount tr) s $ tr : trs

-- |Convert the topmost group of a bottom-up `TRBuf` into a completed
-- top-down report about the group.
currentGroup :: TRBuf -> TestResult
currentGroup (Buf up tc fc s trs) = Group s tc fc (reverse trs)

-- |Derive a new `TRBuf` corresponding to finishing the current group
-- and continuing to accumulate results into its enclosure.
popGroup :: TRBuf -> TRBuf
popGroup trb@(Buf acc _ _ _ _) = addResult acc $ currentGroup trb

-- |Convert a `TRBuf` into a list of top-down `TestResult`s.
closeTRBuf :: TRBuf -> [TestResult]
closeTRBuf (Top _ _ ts) = reverse ts
closeTRBuf b = closeTRBuf $ popGroup b

-- |Record of options which may be specified for running and reporting
-- TLT tests.
data TLTopts = TLTopts {
  optShowPasses :: Bool,
  optQuitAfterFailReport :: Bool
}

-- |Synonym for the elements of the `TLT` state.
type TLTstate = (TLTopts, TRBuf)

-- |Monad transformer for TLT tests.  This layer stores the results
-- from tests as they are executed.
newtype Monad m => TLT m r = TLT { unwrap :: StateT TLTstate m r }

-- |Using `TLT` as a functor.
instance Monad m => Functor (TLT m) where
  fmap f (TLT m) = TLT $ do
    v <- m
    return $ f v

-- |Using `TLT` as an applicative functor.
instance (Monad m, Functor m) => Applicative (TLT m) where
  pure v = TLT $ pure v
  (TLT m1) <*> (TLT m2) = TLT $ do
    f <- m1
    v <- m2
    return (f v)

-- |Standard `Monad`ic operations.
instance (Monad m, Functor m) => Monad (TLT m) where
  -- (>>=) :: TLT m a -> (a -> TLT m b) -> TLT m b
  (TLT m) >>= f = TLT $ m >>= (unwrap . f)

  -- (>>) :: TLT m a -> TLT m b -> TLT m b
  (TLT m1) >> (TLT m2) = TLT $ m1 >> m2

  -- return :: a -> TLT m a
  return v = TLT $ return v

-- |Allow the `TLT` layer to be used from a surrounding transformer.
instance MonadTrans TLT where
  lift = TLT . lift

-- |Facilitate `IO` interaction within or above the the `TLT` layer.
instance MonadIO m => MonadIO (TLT m) where
  liftIO = lift . liftIO

-- |Execute the tests specified in a `TLT` monad, and report the
-- results.
tlt :: MonadIO m => TLT m r -> m ()
tlt (TLT t) = do
  liftIO $ putStrLn "Running tests:"
  (_, (opts, resultsBuf)) <- runStateT t $ (TLTopts False False, Top 0 0 [])
  liftIO $ report opts $ closeTRBuf resultsBuf

-- |Organize the tests in the given subcomputation as a separate group
-- within the test results we will report.
inGroup :: Monad m => String -> TLT m () -> TLT m ()
inGroup name group = do
  (opts, before) <- TLT get
  TLT $ put $ (opts, Buf before 0 0 name [])
  group
  (opts', after) <- TLT $ get
  TLT $ put $ (opts', popGroup after)

{-  Does not work now, but not important to fix immediately.

-- |Allowing the `TLT` layer to be wrapped by the layers it tests,
-- instead of `TLT` wrapping them.

class Monad m => MonadTLT m where
  liftTLT :: (forall m0 . Monad m0 => TLT m0 a) -> m a

instance (MonadTrans m, MonadTLT m0, Monad (m m0)) => MonadTLT (m m0) where
  liftTLT = lift . liftTLT
-}

-- * Specifying individual tests

infix 0 ~:, ~::, ~::-

-- |Name and perform a test of an `Assertion`.
(~:) :: Monad m => String -> Assertion m -> TLT m ()
s ~: a = TLT $ do
  (opts, oldState) <- get
  assessment <- lift a
  put (opts, addResult oldState $ Test s assessment)

-- |Name and perform a test of a (pure) boolean value.
(~::-) :: Monad m => String -> Bool -> TLT m ()
s ~::- b = TLT $ do
  (opts, oldState) <- get
  put (opts, addResult oldState $ Test s $
        if b then [] else [Asserted $ "Expected True but got False"])

-- |Name and perform a test of a boolean value returned by a
-- computation in the wrapped monad @m@.
(~::) :: Monad m => String -> m Bool -> TLT m ()
s ~:: bM = TLT $ do
  b <- lift bM
  (opts, oldState) <- get
  put (opts, addResult oldState $ Test s $
        if b then [] else [Asserted $ "Expected True but got False"])

infix 1 !==,  !/=,  !<,  !>,  !<=,  !>=
infix 1 !==-, !/=-, !<-, !>-, !<=-, !>=-

-- |Transform a binary function on an expected and an actual value
-- (plus a binary generator of a failure message) into an `Assertion`
-- for a pure given actual value.
liftAssertion2Pure ::
  (Monad m) => (a -> a -> Bool) -> (a -> a -> String) -> a -> a -> Assertion m
liftAssertion2Pure tester explainer exp actual = return $
  if (tester exp actual) then [] else [Asserted $ explainer exp actual]

-- |Given an `Assertion` for two pure values (expected and actual),
-- lift it to an `Assertion` expecting the actual value to be returned
-- from a computation.
assertion2PtoM ::
  (Monad m) => (a -> a -> Assertion m) -> a -> m a -> Assertion m
assertion2PtoM pa exp actualM = do actual <- actualM
                                   pa exp actual

-- |Transform a binary function on expected and actual values (plus
-- a generator of a failure message) into an `Assertion` where the
-- actual value is to be returned from a subcomputation.
liftAssertion2M ::
  (Monad m) => (a -> a -> Bool) -> (a -> a -> String) -> a -> m a -> Assertion m
liftAssertion2M tester explainer exp actualM =
  let assertPure = liftAssertion2Pure tester explainer exp
  in do actual <- actualM
        assertPure actual

-- |Assert that two values are equal.
(!==-) :: (Monad m, Eq a, Show a) => a -> a -> Assertion m
(!==-) = liftAssertion2Pure (==) $
  \ exp actual -> "Expected " ++ show exp ++ " but got " ++ show actual

-- |Assert that a calculated value is as expected.
(!==) :: (Monad m, Eq a, Show a) => a -> m a -> Assertion m
(!==) = assertion2PtoM (!==-)

-- |Assert that two values are not equal.
(!/=-) :: (Monad m, Eq a, Show a) => a -> a -> Assertion m
(!/=-) = liftAssertion2Pure (/=) $
  \ exp actual ->
    "Expected other than " ++ show exp ++ " but got " ++ show actual

-- |Assert that a calculated value differs from some known value.
(!/=) :: (Monad m, Eq a, Show a) => a -> m a -> Assertion m
(!/=) = assertion2PtoM (!/=-)

-- |Assert that a given boundary is strictly less than some value.
(!<-) :: (Monad m, Ord a, Show a) => a -> a -> Assertion m
(!<-) = liftAssertion2Pure (<) $
  \ exp actual ->
    "Lower bound (open) is " ++ show exp ++ " but got " ++ show actual

-- |Assert that a given, constant boundary is strictly less than some
-- calculated value.
(!<) :: (Monad m, Ord a, Show a) => a -> m a -> Assertion m
(!<) = assertion2PtoM (!<-)

-- |Assert that a given boundary is strictly less than some value.
(!>-) :: (Monad m, Ord a, Show a) => a -> a -> Assertion m
(!>-) = liftAssertion2Pure (>) $
  \ exp actual ->
    "Upper bound (open) is " ++ show exp ++ " but got " ++ show actual

-- |Assert that a given, constant boundary is strictly less than some
-- calculated value.
(!>) :: (Monad m, Ord a, Show a) => a -> m a -> Assertion m
(!>) = assertion2PtoM (!>-)

-- |Assert that a given boundary is strictly less than some value.
(!<=-) :: (Monad m, Ord a, Show a) => a -> a -> Assertion m
(!<=-) = liftAssertion2Pure (<=) $
  \ exp actual ->
    "Lower bound (closed) is " ++ show exp ++ " but got " ++ show actual

-- |Assert that a given, constant boundary is strictly less than some
-- calculated value.
(!<=) :: (Monad m, Ord a, Show a) => a -> m a -> Assertion m
(!<=) = assertion2PtoM (!<=-)

-- |Assert that a given boundary is strictly less than some value.
(!>=-) :: (Monad m, Ord a, Show a) => a -> a -> Assertion m
(!>=-) = liftAssertion2Pure (>=) $
  \ exp actual ->
    "Upper bound (closed) is " ++ show exp ++ " but got " ++ show actual

-- |Assert that a given, constant boundary is strictly less than some
-- calculated value.
(!>=) :: (Monad m, Ord a, Show a) => a -> m a -> Assertion m
(!>=) = assertion2PtoM (!>=-)

-- |Transform a unary function on a value (plus a generator of a
-- failure message) into a unary `Assertion` function for a pure given
-- actual value.
liftAssertionPure ::
  (Monad m) => (a -> Bool) -> (a -> String) -> a -> Assertion m
liftAssertionPure tester explainer actual = return $
  if (tester actual) then [] else [Asserted $ explainer actual]

-- |Given an `Assertion` for a pure (actual) value, lift it to an
-- `Assertion` expecting the value to be returned from a computation.
assertionPtoM :: (Monad m) => (a -> Assertion m) -> m a -> Assertion m
assertionPtoM pa actualM = do actual <- actualM
                              pa actual

-- |Transform a unary function on an actual value (plus a generator
-- of a failure message) into an `Assertion` where the value is to be
-- returned from a subcomputation.
liftAssertionM ::
  (Monad m) => (a -> Bool) -> (a -> String) -> m a -> Assertion m
liftAssertionM tester explainer actualM =
  let assertPure = liftAssertionPure tester explainer
  in do actual <- actualM
        assertPure actual

-- |Assert that a pure foldable structure (such as a list) is empty.
emptyP :: (Monad m, Foldable t) => t a -> Assertion m
emptyP = liftAssertionPure null
           (\ _ -> "Expected empty structure but got non-empty")

-- |Assert that a foldable structure (such as a list) returned from a
-- computation is empty.
empty :: (Monad m, Foldable t) => m (t a) -> Assertion m
empty = assertionPtoM emptyP

-- |Assert that a pure foldable structure (such as a list) is nonempty.
nonemptyP :: (Monad m, Foldable t) => t a -> Assertion m
nonemptyP = liftAssertionPure (not . null)
              (\ _ -> "Expected non-empty structure but got empty")

-- |Assert that a foldable structure (such as a list) returned from a
-- computation is non-empty.
nonempty :: (Monad m, Foldable t) => m (t a) -> Assertion m
nonempty = assertionPtoM nonemptyP

-- |Assert that a `Maybe` value is `Nothing`.
nothingP :: Monad m => Maybe a -> Assertion m
nothingP = liftAssertionPure isNothing
           (\ _ -> "Expected empty Maybe value but got non-Nothing")

-- |Assert that a `Maybe` result ofa computation is `Nothing`.
nothing :: Monad m => m (Maybe a) -> Assertion m
nothing = assertionPtoM nothingP
