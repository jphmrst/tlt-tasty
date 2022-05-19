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
tests to be specified in some sort of formal list of tests.  Rather,
tests are simply commands in a monad stack which includes the
transformer layer @Test.TLT@.

This Haddock page is the main piece of documentation; or see also the
GitHub repository <https://github.com/jphmrst/TLT/>.

-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Test.TLT (
  -- * The TLT transformer
  TLT, tlt, MonadTLT, liftTLT,
  -- ** Session options
  reportAllTestResults, setExitAfterFailDisplay,
  -- * Writing tests
  Assertion,
  -- ** `TLT` commands
  (~:), (~::), (~::-), tltFail, inGroup,
  -- ** Assertions
  -- *** About the values of pure expressions of `Eq`- and `Ord`-type
  (@==),  (@/=),  (@<),  (@>),  (@<=),  (@>=),
  -- *** About monadic computations returing `Eq`s and `Ord`s
  (@==-), (@/=-), (@<-), (@>-), (@<=-), (@>=-),
  -- *** About list values
  empty, nonempty, emptyP, nonemptyP,
  -- *** About `Maybe` values
  nothing, nothingP, assertFailed, assertSuccess,
  -- ** Building new assertions
  -- *** Unary assertions
  liftAssertionPure, assertionPtoM, liftAssertionM,
  -- *** Binary assertions
  liftAssertion2Pure, assertion2PtoM, liftAssertion2M

  ) where

import Data.Maybe
import Control.Exception
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.ST.Trans
import Control.Monad.Trans.Class
-- import Control.Monad.Trans.Either
import Control.Monad.Trans.Free
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Resource
import Control.Monad.Trans.State.Strict
import qualified Control.Monad.Trans.State.Lazy as SL
import qualified Control.Monad.Trans.Writer.Lazy as WL
import qualified Control.Monad.Trans.Writer.Strict as WS
import System.Console.ANSI
import System.Exit
import qualified Test.Tasty.Providers as TTP

-- * Results of tests

-- |Reasons why a test might fail.
data TestFail = Asserted String
                -- ^ A failure arising from an `Assertion` which is not met.
              | Erred String
                -- ^ A failure associated with a call to a Haskell
                -- function triggering an error.

formatFail :: TestFail -> String
formatFail (Asserted s) = s
formatFail (Erred s) = "Assertion raised exception: " ++ s

-- |An assertion is a computation (typically in the monad wrapped by
-- `TLT`) which returns a list of zero of more reasons for the failure
-- of the assertion.  A successful computation returns an empty list:
-- no reasons for failure, hence success.
type Assertion m = m [TestFail]

-- |Hierarchical structure holding the result of running tests,
-- possibly grouped into tests.
data TestResult = Test String [TestFail]
                | Group String Int Int [TestResult]
                  -- ^ The `Int`s are respectively the total number of
                  -- tests executed, and total number of failures
                  -- detected.

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
  deriving (Functor, Applicative, Monad, MonadTrans, MonadIO)

{- ------------------------------------------------------------ -}

-- |Extending `TLT` operations across other monad transformers.  For
-- easiest and most flexible testing, declare the monad transformers
-- of your application as instances of this class.
class (Monad m, Monad n) => MonadTLT m n | m -> n where
  -- |Lift TLT operations within a monad transformer stack.  Note that
  -- with enough transformer types included in this class, the
  -- @liftTLT@ function should usually be unnecessary: the commands in
  -- this module which actually configure testing, or specify a test,
  -- already @liftTLT@ their own result.  So they will all act as
  -- top-level transformers in @MonadTLT@.
  liftTLT :: TLT n a -> m a

instance Monad m => MonadTLT (TLT m) m where
  liftTLT = id

instance (MonadTLT m n, Functor f) => MonadTLT (FreeT f m) n where
    liftTLT = lift . liftTLT

instance MonadTLT m n => MonadTLT (IdentityT m) n where
  liftTLT = lift . liftTLT

instance MonadTLT m n => MonadTLT (MaybeT m) n where
  liftTLT = lift . liftTLT

instance MonadTLT m n => MonadTLT (ReaderT r m) n where
  liftTLT = lift . liftTLT

instance MonadTLT m n => MonadTLT (ResourceT m) n where
  liftTLT = lift . liftTLT

instance MonadTLT m n => MonadTLT (StateT s m) n where
  liftTLT = lift . liftTLT

instance MonadTLT m n => MonadTLT (SL.StateT s m) n where
  liftTLT = lift . liftTLT

instance MonadTLT m n => MonadTLT (STT s m) n where
  liftTLT = lift . liftTLT

instance (MonadTLT m n, Monoid w) => MonadTLT (WL.WriterT w m) n where
  liftTLT = lift . liftTLT

instance (MonadTLT m n, Monoid w) => MonadTLT (WS.WriterT w m) n where
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
reportAllTestResults :: MonadTLT m n => Bool -> m ()
reportAllTestResults b = liftTLT $ TLT $ do
  (opts, tr) <- get
  put $ (opts `withShowPasses` b, tr)

-- |This function controls whether `tlt` will exit after displaying
-- test results which include at least one failing test.  By default,
-- it will exit in this situation.  The idea is that a test suite can
-- be broken into parts when it makes sense to run the latter parts
-- only when the former parts all pass.
setExitAfterFailDisplay :: MonadTLT m n => Bool -> m ()
setExitAfterFailDisplay b = liftTLT $ TLT $ do
  (opts, tr) <- get
  put $ (opts `withExitAfterFail` b, tr)

-- |Report a failure.  Useful in pattern-matching cases which are
-- entirely not expected.
tltFail :: MonadTLT m n => String -> String -> m ()
desc `tltFail` detail = liftTLT $ TLT $ do
  (opts, before) <- get
  let after = addResult before $ Test desc [Asserted detail]
  put (opts, after)

-- |Organize the tests in the given subcomputation as a separate group
-- within the test results we will report.
inGroup :: MonadTLT m n => String -> m a -> m a
inGroup name group = do
  (opts, before) <- liftTLT $ TLT get
  liftTLT $ TLT $ put $ (opts, Buf before 0 0 name [])
  result <- group
  (opts', after) <- liftTLT $ TLT $ get
  liftTLT $ TLT $ put $ (opts', popGroup after)
  return result

-- * Specifying individual tests

infix 0 ~:, ~::, ~::-

-- |Label and perform a test of an `Assertion`.
--
-- ===== Example
--
-- > test :: Monad m => TLT m ()
-- > test = do
-- >   "2 is 2 as result" ~: 2 @== return 2    -- This test passes.
-- >   "2 not 3" ~: 2 @/=- 3                   -- This test fails.
(~:) :: MonadTLT m n => String -> Assertion m -> m ()
s ~: a = do
  (opts, oldState) <- liftTLT $ TLT $ get
  assessment <- a
  liftTLT $ TLT $ put (opts, addResult oldState $ Test s assessment)

-- |Label and perform a test of a (pure) boolean value.
--
-- ===== Example
--
-- > test :: Monad m => TLT m ()
-- > test = do
-- >   "True passes" ~::- return True                 -- This test passes.
-- >   "2 is 2 as single Bool" ~::- return (2 == 2)   -- This test passes.
-- >   "2 is 3!?" ~::- myFn 4 "Hammer"                -- Passes if myFn (which
-- >                                                  -- must be monadic)
-- >                                                  -- returns True.
(~::-) :: MonadTLT m n => String -> Bool -> m ()
s ~::- b = do
  (opts, oldState) <- liftTLT $ TLT $ get
  liftTLT $ TLT $ put (opts, addResult oldState $ Test s $
        if b then [] else [Asserted $ "Expected True but got False"])

-- |Label and perform a test of a boolean value returned by a
-- computation in the wrapped monad @m@.
--
-- ===== Example
--
-- > test :: Monad m => TLT m ()
-- > test = do
-- >   "True passes" ~::- True               -- This test passes.
-- >   "2 is 2 as single Bool" ~::- 2 == 2   -- This test passes.
-- >   "2 is 3!?" ~::- 2 == 2                -- This test fails.
(~::) :: MonadTLT m n => String -> m Bool -> m ()
s ~:: bM = do
  b <- bM
  (opts, oldState) <- liftTLT $ TLT $ get
  liftTLT $ TLT $ put (opts, addResult oldState $ Test s $
        if b then [] else [Asserted $ "Expected True but got False"])

infix 1 @==,  @/=,  @<,  @>,  @<=,  @>=
infix 1 @==-, @/=-, @<-, @>-, @<=-, @>=-

-- |Transform a binary function on an expected and an actual value
-- (plus a binary generator of a failure message) into an `Assertion`
-- for a pure given actual value.
--
-- ===== Example
--
-- TLT's scalar-testing operators like @\@==-@ are defined with this
-- function:
--
-- > (@==-) :: (Monad m, Eq a, Show a) => a -> a -> Assertion m
-- > (@==-) = liftAssertion2Pure (==) $
-- >   \ exp actual -> "Expected " ++ show exp ++ " but got " ++ show actual
--
-- The `(==)` operator tests equality, and the result here allows the
-- assertion that a value should be exactly equal to a target.  The
-- second argument formats the detail reported when the assertion
-- fails.
liftAssertion2Pure ::
  (Monad m) => (a -> a -> Bool) -> (a -> a -> String) -> a -> a -> Assertion m
liftAssertion2Pure tester explainer exp actual = return $
  if (tester exp actual) then [] else [Asserted $ explainer exp actual]

-- |Given an `Assertion` for two pure values (expected and actual),
-- lift it to an `Assertion` expecting the actual value to be returned
-- from a computation.
--
-- ===== Examples
--
-- The TLT assertion `(@==)` lifts `(@==-)` from expecting a pure
-- actual result to expecting a computation returning a value to test.
--
-- > (@==) :: (Monad m, Eq a, Show a) => a -> m a -> Assertion m
-- > (@==) = assertion2PtoM (@==-)
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

-- |Assert that two values are equal.  This assertion takes an
-- expected and an actual /value/; see `(@==)` to compare the result
-- of a /monadic computation/ to an expected value.
--
-- ===== Examples
--
-- > test :: Monad m => TLT m ()
-- > test = do
-- >   "Make sure that 2 is still equal to itself" ~: 2 @==- 2
-- >   "Make sure that there are four lights" ~: 4 @==- length lights
(@==-) :: (Monad m, Eq a, Show a) => a -> a -> Assertion m
(@==-) = liftAssertion2Pure (==) $
  \ exp actual -> "Expected " ++ show exp ++ " but got " ++ show actual

-- |Assert that a calculated value is as expected.  This assertion
-- compare the result of a /monadic computation/ to an expected value;
-- see `(@==-)` to compare an /actual value/ to the expected value.
--
-- ===== Examples
--
-- > test :: Monad m => TLT m ()
-- > test = do
-- >   "Make sure that 2 is still equal to itself" ~: 2 @== return 2
-- >   "Make sure that there are four lights" ~: 4 @== countLights
-- >                                             -- where countLights :: m Int
(@==) :: (Monad m, Eq a, Show a) => a -> m a -> Assertion m
(@==) = assertion2PtoM (@==-)

-- |Assert that two values are not equal.  This assertion takes an
-- expected and an actual /value/; see `(@/=)` to compare the result
-- of a /monadic computation/ to an expected value.
(@/=-) :: (Monad m, Eq a, Show a) => a -> a -> Assertion m
(@/=-) = liftAssertion2Pure (/=) $
  \ exp actual ->
    "Expected other than " ++ show exp ++ " but got " ++ show actual

-- |Assert that a calculated value differs from some known value.
-- This assertion compares the result of a /monadic computation/ to an
-- expected value; see `(@/=-)` to compare an /actual value/ to the
-- expected value.
(@/=) :: (Monad m, Eq a, Show a) => a -> m a -> Assertion m
(@/=) = assertion2PtoM (@/=-)

-- |Assert that a given boundary is strictly less than some value.
-- This assertion takes an expected and an actual /value/; see `(@<)`
-- to compare the result of a /monadic computation/ to an expected
-- value.
(@<-) :: (Monad m, Ord a, Show a) => a -> a -> Assertion m
(@<-) = liftAssertion2Pure (<) $
  \ exp actual ->
    "Lower bound (open) is " ++ show exp ++ " but got " ++ show actual

-- |Assert that a given, constant boundary is strictly less than some
-- calculated value.  This assertion compares the result of a /monadic
-- computation/ to an expected value; see `(@<-)` to compare an
-- /actual value/ to the expected value.
(@<) :: (Monad m, Ord a, Show a) => a -> m a -> Assertion m
(@<) = assertion2PtoM (@<-)

-- |Assert that a given boundary is strictly less than some value.
-- This assertion takes an expected and an actual /value/; see `(@>)`
-- to compare the result of a /monadic computation/ to an expected
-- value.
(@>-) :: (Monad m, Ord a, Show a) => a -> a -> Assertion m
(@>-) = liftAssertion2Pure (>) $
  \ exp actual ->
    "Upper bound (open) is " ++ show exp ++ " but got " ++ show actual

-- |Assert that a given, constant boundary is strictly less than some
-- calculated value.  This assertion compares the result of a /monadic
-- computation/ to an expected value; see `(@>-)` to compare an
-- /actual value/ to the expected value.
(@>) :: (Monad m, Ord a, Show a) => a -> m a -> Assertion m
(@>) = assertion2PtoM (@>-)

-- |Assert that a given boundary is strictly less than some value.
-- This assertion takes an expected and an actual /value/; see `(@<=)`
-- to compare the result of a /monadic computation/ to an expected
-- value.
(@<=-) :: (Monad m, Ord a, Show a) => a -> a -> Assertion m
(@<=-) = liftAssertion2Pure (<=) $
  \ exp actual ->
    "Lower bound (closed) is " ++ show exp ++ " but got " ++ show actual

-- |Assert that a given, constant boundary is strictly less than some
-- calculated value.  This assertion compares the result of a /monadic
-- computation/ to an expected value; see `(@<=-)` to compare an
-- /actual value/ to the expected value.
(@<=) :: (Monad m, Ord a, Show a) => a -> m a -> Assertion m
(@<=) = assertion2PtoM (@<=-)

-- |Assert that a given boundary is strictly less than some value.
-- This assertion takes an expected and an actual /value/; see `(@>=)`
-- to compare the result of a /monadic computation/ to an expected
-- value.
(@>=-) :: (Monad m, Ord a, Show a) => a -> a -> Assertion m
(@>=-) = liftAssertion2Pure (>=) $
  \ exp actual ->
    "Upper bound (closed) is " ++ show exp ++ " but got " ++ show actual

-- |Assert that a given, constant boundary is strictly less than some
-- calculated value.  This assertion compares the result of a /monadic
-- computation/ to an expected value; see `(@>=-)` to compare an
-- /actual value/ to the expected value.
(@>=) :: (Monad m, Ord a, Show a) => a -> m a -> Assertion m
(@>=) = assertion2PtoM (@>=-)

-- |This assertion always fails with the given message.
assertFailed :: Monad m => String -> Assertion m
assertFailed msg = return [Asserted msg]

-- |This assertion always succeeds.
assertSuccess :: Monad m => Assertion m
assertSuccess = return []

-- |Transform a unary function on a value (plus a generator of a
-- failure message) into a unary function returning an `Assertion` for
-- a pure given actual value.
--
-- ===== Example
--
-- The TLT assertion `emptyP` is built from the `Traversable` predicate
-- `null`
--
-- > emptyP :: (Monad m, Traversable t) => t a -> Assertion m
-- > emptyP = liftAssertionPure null
-- >            (\ _ -> "Expected empty structure but got non-empty")

liftAssertionPure ::
  (Monad m) => (a -> Bool) -> (a -> String) -> a -> Assertion m
liftAssertionPure tester explainer actual = return $
  if (tester actual) then [] else [Asserted $ explainer actual]

-- |Given an `Assertion` for a pure (actual) value, lift it to an
-- `Assertion` expecting the value to be returned from a computation.
--
-- ===== Example
--
-- The TLT assertion `empty` on monadic computations returning lists
-- is defined in terms of the corresponging assertion on pure
-- list-valued expressions.
--
-- > empty :: (Monad m, Traversable t) => m (t a) -> Assertion m
-- > empty = assertionPtoM emptyP
assertionPtoM :: (Monad m) => (a -> Assertion m) -> m a -> Assertion m
assertionPtoM pa actualM = do actual <- actualM
                              pa actual

-- |Transform a unary function on an actual value (plus a generator of
-- a failure message) into an `Assertion` where the value is to be
-- returned from a subcomputation.
liftAssertionM ::
  (Monad m) => (a -> Bool) -> (a -> String) -> m a -> Assertion m
liftAssertionM tester explainer actualM =
  let assertPure = liftAssertionPure tester explainer
  in do actual <- actualM
        assertPure actual

-- |Assert that a pure traversable structure (such as a list) is
-- empty.
emptyP :: (Monad m, Traversable t) => t a -> Assertion m
emptyP = liftAssertionPure null
           (\ _ -> "Expected empty structure but got non-empty")

-- |Assert that a traversable structure (such as a list) returned from
-- a computation is empty.
empty :: (Monad m, Traversable t) => m (t a) -> Assertion m
empty = assertionPtoM emptyP

-- |Assert that a pure traversable structure (such as a list) is
-- nonempty.
nonemptyP :: (Monad m, Traversable t) => t a -> Assertion m
nonemptyP = liftAssertionPure (not . null)
              (\ _ -> "Expected non-empty structure but got empty")

-- |Assert that a traversable structure (such as a list) returned from
-- a computation is non-empty.
nonempty :: (Monad m, Traversable t) => m (t a) -> Assertion m
nonempty = assertionPtoM nonemptyP

-- |Assert that a `Maybe` value is `Nothing`.
nothingP :: Monad m => Maybe a -> Assertion m
nothingP = liftAssertionPure isNothing
           (\ _ -> "Expected empty Maybe value but got non-Nothing")

-- |Assert that a `Maybe` result ofa computation is `Nothing`.
nothing :: Monad m => m (Maybe a) -> Assertion m
nothing = assertionPtoM nothingP
