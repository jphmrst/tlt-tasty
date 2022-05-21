
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

import Data.Typeable
import Test.TLT
import Test.Tasty
import Test.Tasty.Providers
import Test.TastyTLT
import Control.Monad.Trans.Identity
import Control.Monad.Trans

-- The next three definitions are taken from the example in the Tasty
-- documentation, <https://hackage.haskell.org/package/tasty>.
main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "TastyTLTTests" [singleTest "test" test]


test :: TLT IO ()
test = do
  "True passes" ~::- True
  "2 is 2 as single Bool" ~::- 2 == 2
  inGroup "== assertions" $ do
    inGroup "pure" $ do
      "2 is 2 as pure assertion" ~: 2 @==- 2
    inGroup "monadic" $ do
      "2 is 2 as result" ~: 2 @== return 2
  inGroup "/= pure assertions" $ do
    "2 not 3" ~: 2 @/=- 3
    "2 not 4" ~: 2 @/=- 4
  "2 not 3 as result" ~: 2 @/= return 3
