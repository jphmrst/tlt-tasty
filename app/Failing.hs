import Test.TLT
import Test.Tasty
import Test.Tasty.TLT

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "TastyTLTTests" [tltTest "Failing test" test]

test :: Monad m => TLT m ()
test = do
  "True passes" ~::- True
  "2 is 3 as single Bool" ~::- 2 == 3
  "2 is 2 as single Bool" ~::- 2 == 2
  inGroup "== assertions" $ do
    inGroup "pure" $ do
      "2 is 3 as pure assertion" ~: 2 @==- 3
      "2 is 2 as pure assertion" ~: 2 @==- 2
    inGroup "monadic" $ do
      "2 is 3 as result" ~: 2 @== return 3
      "2 is 2 as result" ~: 2 @== return 2
  inGroup "/= pure assertions" $ do
    "2 not 3" ~: 2 @/=- 3
    "2 not 2" ~: 2 @/=- 2
  "2 not 3 as result" ~: 2 @/= return 3
  "2 not 2 as result" ~: 2 @/= return 2
