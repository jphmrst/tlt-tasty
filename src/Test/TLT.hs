{-|
Module      : TLT
Description : Testing in a monad transformer layer
Copyright   : (c) John Maraist, 2022
License     : GPL3
Maintainer  : haskell-tlt@maraist.org
Stability   : experimental
Portability : POSIX

TLT is a small unit test system oriented towards examining
intermediate results of computations in monad transformers.  It is
intended to be lightweight for the programmer, and does not require
tests to be specified is some sort of formal list of tests.  Rather,
tests are simply commands in a monad stack which includes the
@Test.TLT@ transformer layer.  This Haddock page is the main piece of
documentation; or see also the GitHub repository
<https://github.com/jphmrst/TLT/>.

-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

module Test.TLT (
  -- * Overview

  -- |A TLT test is a command in the `TLT` monad transformer.  There
  -- is no separation between the specification and execution of a
  -- test; TLT makes no record of an executable test itself, only of
  -- its result.  So in the main instance for testing, the core `IO`
  -- monad should be wrapped in the `TLT` transformer, and in whatever
  -- other layers are also to be tested.
  --
  -- In TLT, all tests are associated with a string which names or
  -- otherwise describes the test.  Each test is introduced with one
  -- of the @~:@, @~::@, or @~::-@ infix operators.
  --
  -- The simplest tests simply look for a `True` boolean value.  These
  -- tests are introduced with @~::@ or @~::-@.  The difference
  -- between the two is whether the boolean value is the result of a
  -- pure `Bool` expression, or whether it is returned as the result
  -- of a computation.  In TLT, we distinguish between the two cases
  -- by including a trailing hyphen @-@ to operators on pure
  -- expressions, and omitting the hyphen from operators on monadic
  -- arguments.  So these two tests will both pass,
  --
  -- > "2 is 2 as single Bool" ~::- 2 == 2
  -- > "2 is 2 a returned Bool" ~:: return $ 2 == 2
  --
  -- The @~:@ operator introduces a more general form of test.  The
  -- right-hand side of @~:@ should be an `Assertion` formed with one
  -- of TLT's built-in assertion operators, or returned from a
  -- package's custom assertions.  `Assertion`s can give more detailed
  -- failure information then simple `Bool`s.  A hyphen or @P@
  -- suffixes assertion operators which operate on pure values instead
  -- of the results of monadic computations (as with @~::@ and
  -- @~::-@).  TLT provides these assertion operators:
  --
  -- +--------------------------------+----------------------------------------+
  -- | Operator                       | Meaning                                |
  -- +================================+========================================+
  -- | /expected/ @(!==)@ /monadic/   | The actual result must be equal        |
  -- +--------------------------------+ to the given expected result.          |
  -- | /expected/ @(!==-)@ /expr/     |                                        |
  -- +--------------------------------+----------------------------------------+
  -- | /unexpected/ @(!/=)@ /monadic/ | The actual result must differ          |
  -- +--------------------------------+ from the given unexpected result.      |
  -- | /unexpected/ @(!/=-)@ /expr/   |                                        |
  -- +--------------------------------+----------------------------------------+
  -- | /expected/ @(!<)@ /monadic/    | The actual result must be greater      |
  -- +--------------------------------+ than the given lower bound.            |
  -- | /expected/ @(!<-)@ /expr/      |                                        |
  -- +--------------------------------+----------------------------------------+
  -- | /expected/ @(!>)@ /monadic/    | The actual result must be less         |
  -- +--------------------------------+ than the given upper bound.            |
  -- | /expected/ @(!>-)@ /expr/      |                                        |
  -- +--------------------------------+----------------------------------------+
  -- | /expected/ @(!<=)@ /monadic/   | The actual result must be greater than |
  -- +--------------------------------+ or equal to the given lower bound.     |
  -- | /expected/ @(!<=-)@ /expr/     |                                        |
  -- +--------------------------------+----------------------------------------+
  -- | /expected/ @(!>=)@ /monadic/   | The actual result must be less than    |
  -- +--------------------------------+ or equal to the given upper bound.     |
  -- | /expected/ @(!>=-)@ /expr/     |                                        |
  -- +--------------------------------+----------------------------------------+
  -- | @empty@ /monadic/              | The actual result must be an empty     |
  -- +--------------------------------+ `Traversable` structure.               |
  -- | @emptyP@ /expr/                |                                        |
  -- +--------------------------------+----------------------------------------+
  -- | @nonempty@ /monadic/           | The actual result must be a nonempty   |
  -- +--------------------------------+ `Traversable` structure.               |
  -- | @nonemptyP@ /expr/             |                                        |
  -- +--------------------------------+----------------------------------------+
  -- | @nothing@ /monadic/            | The actual result must be `Nothing`    |
  -- +--------------------------------+ (in a `Maybe`-typed value)             |
  -- | @nothingP@ /expr/              |                                        |
  -- +--------------------------------+----------------------------------------+
  --
  -- Note that although the assertions are in pairs of one for testing
  -- a pure expression value, and one for testing the result returned
  -- from a monadic computation, in all of the builtin binary
  -- assertions the /expected/ value argument is always a pure value,
  -- not itself monadic.
  --
  -- The `inGroup` function allows related tests to be reported as a
  -- group.  The function takes two arguments, a `String` name for the
  -- group, and the `TLT` computation housing its tests.  Groups have
  -- impact only in terms of organizing the output you see in the
  -- final report of tests run.
  --
  -- Finally, it is straightforward to write new `Assertion`s for
  -- project-specific test criteria: they are simply functions
  -- returning monadic values.  There are several functions in the
  -- final section of this document which transform pure predicates
  -- into `Assertion`s, or which transform one form of `Assertion`
  -- into another.
  --
  -- The source repository for TLT lives at
  -- <https://github.com/jphmrst/tlt>.

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
  -- > - 2 is 3 as single Bool: FAIL Expected True but got False
  -- > - == assertions:
  -- >   - pure:
  -- >     - 2 is 3 as pure assertion: FAIL Expected 2 but got 3
  -- >   - monadic:
  -- >     - 2 is 3 as result: FAIL Expected 2 but got 3
  -- > - /= pure assertions:
  -- >   - 2 not 2: FAIL Expected other than 2 but got 2
  -- > - 2 not 2 as result: FAIL Expected other than 2 but got 2
  -- > Found 5 errors in 11 tests; exiting
  --
  -- Note that only failing tests appear.  This can be configured in the
  -- @test@ command: add a call at the beginning of @test@ to
  -- @reportAllTestResults@ to control this behavior:
  --
  -- > test :: Monad m => TLT m ()
  -- > test = do
  -- >   reportAllTestResults True
  -- >   "True passes" ~::- True
  -- >   ...
  --
  -- and the output will be
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

  -- * The TLT transformer
  TLT, tlt, MonadTLT, liftTLT,
  -- ** Session options
  reportAllTestResults, setExitAfterFailDisplay,
  -- * Writing tests
  Assertion,
  -- ** `TLT` commands
  (~:), (~::), (~::-), inGroup,
  -- ** Assertions
  (!==),  (!/=),  (!<),  (!>),  (!<=),  (!>=),
  (!==-), (!/=-), (!<-), (!>-), (!<=-), (!>=-),
  empty, nonempty, nothing, emptyP, nonemptyP, nothingP,
  -- ** Building new assertions
  -- *** Unary assertions
  liftAssertionPure, assertionPtoM, liftAssertionM,
  -- *** Binary assertions
  liftAssertion2Pure, assertion2PtoM, liftAssertion2M

  ) where

import Data.Maybe
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.ST.Trans
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
report (TLTopts showPasses exitAfterFailDisplay) trs =
  let fails = totalFailCount trs
      tests = totalTestCount trs
  in do report' "" trs
        if fails > 0
          then do boldRed
                  putStrLn $
                    "Found " ++ show fails ++ " error"
                      ++ (if fails > 1 then "s" else "")
                      ++ " in " ++ show tests ++ " tests; exiting"
                  mediumBlack
                  when exitAfterFailDisplay exitFailure
          else do boldGreen
                  putStrLn $ show tests ++ " test"
                    ++ (if tests > 1 then "s" else "")
                    ++ " passing."
                  mediumBlack
  where report' ind trs = forM_ trs $ \ tr ->
          when (failCount tr > 0 || showPasses) $
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

boldBlack = setSGR [
  SetColor Foreground Vivid Black, SetConsoleIntensity BoldIntensity ]
boldRed = setSGR [
  SetColor Foreground Vivid Red, SetConsoleIntensity BoldIntensity ]
boldGreen = setSGR [
  SetColor Foreground Vivid Green, SetConsoleIntensity BoldIntensity ]

mediumRed = setSGR [
  SetColor Foreground Vivid Red, SetConsoleIntensity NormalIntensity ]
mediumGreen = setSGR [
  SetColor Foreground Vivid Green, SetConsoleIntensity NormalIntensity ]
mediumBlue = setSGR [
  SetColor Foreground Vivid Blue, SetConsoleIntensity NormalIntensity ]
mediumBlack = setSGR [
  SetColor Foreground Vivid Black, SetConsoleIntensity NormalIntensity ]

greenPass = do
  mediumBlue
  putStr "Pass"
  mediumBlack

redFail = do
  boldRed
  putStr "FAIL"
  mediumBlack

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

-- |Default initial options
defaultOpts = TLTopts False True

-- |Update the display of showing passes in a `TLTopts` record.
withShowPasses :: TLTopts -> Bool -> TLTopts
withShowPasses (TLTopts _ f) b = TLTopts b f

-- |Update the display of showing passes in a `TLTopts` record.
withExitAfterFail :: TLTopts -> Bool -> TLTopts
withExitAfterFail (TLTopts p _) b = TLTopts p b

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

-- |Allowing the `TLT` layer to be wrapped by the layers it tests,
-- instead of `TLT` wrapping them.

{- ------------------------------------------------------------ -}

class (Monad m, Monad n) => MonadTLT m n | m -> n where
  liftTLT :: TLT n a -> m a

instance Monad m => MonadTLT (TLT m) m where
  liftTLT = id

{- TODO Add many inferences of standard classes being MonadTLT -}

instance MonadTLT m n => MonadTLT (STT s m) n where
  liftTLT = lift . liftTLT

{- ------------------------------------------------------------ -}

-- |Execute the tests specified in a `TLT` monad, and report the
-- results.
tlt :: MonadIO m => TLT m r -> m ()
tlt (TLT t) = do
  liftIO $ putStrLn "Running tests:"
  (_, (opts, resultsBuf)) <- runStateT t $ (defaultOpts, Top 0 0 [])
  liftIO $ report opts $ closeTRBuf resultsBuf

-- |This function controls whether `tlt` will report only tests which
-- fail, suppressing any display of tests which pass, or else report
-- the results of all tests.  The default is the former: the idea is
-- that no news should be good news, with the programmer bothered only
-- with problems which need fixing.
reportAllTestResults :: Monad m => Bool -> TLT m ()
reportAllTestResults b = TLT $ do
  (opts, tr) <- get
  put $ (opts `withShowPasses` b, tr)

-- |This function controls whether `tlt` will exit after displaying
-- test results which include at least one failing test.  By default,
-- it will exit in this situation.  The idea is that a test suite can
-- be broken into parts when it makes sense to run the latter parts
-- only when the former parts all pass.
setExitAfterFailDisplay :: Monad m => Bool -> TLT m ()
setExitAfterFailDisplay b = TLT $ do
  (opts, tr) <- get
  put $ (opts `withExitAfterFail` b, tr)

-- |Organize the tests in the given subcomputation as a separate group
-- within the test results we will report.
inGroup :: MonadTLT m n => String -> m () -> m ()
inGroup name group = do
  (opts, before) <- liftTLT $ TLT get
  liftTLT $ TLT $ put $ (opts, Buf before 0 0 name [])
  group
  (opts', after) <- liftTLT $ TLT $ get
  liftTLT $ TLT $ put $ (opts', popGroup after)

-- * Specifying individual tests

infix 0 ~:, ~::, ~::-

-- |Label and perform a test of an `Assertion`.
(~:) :: MonadTLT m n => String -> Assertion m -> m ()
s ~: a = do
  (opts, oldState) <- liftTLT $ TLT $ get
  assessment <- a
  liftTLT $ TLT $ put (opts, addResult oldState $ Test s assessment)

-- |Label and perform a test of a (pure) boolean value.
(~::-) :: MonadTLT m n => String -> Bool -> m ()
s ~::- b = do
  (opts, oldState) <- liftTLT $ TLT $ get
  liftTLT $ TLT $ put (opts, addResult oldState $ Test s $
        if b then [] else [Asserted $ "Expected True but got False"])

-- |Label and perform a test of a boolean value returned by a
-- computation in the wrapped monad @m@.
(~::) :: MonadTLT m n => String -> m Bool -> m ()
s ~:: bM = do
  b <- bM
  (opts, oldState) <- liftTLT $ TLT $ get
  liftTLT $ TLT $ put (opts, addResult oldState $ Test s $
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
-- failure message) into a unary function returning an `Assertion` for
-- a pure given actual value.
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
