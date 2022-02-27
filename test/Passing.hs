
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

import Test.TLT
import Control.Monad.Trans.Identity
import Control.Monad.Trans

main :: IO ()
main = do
  tlt test
  tlt ttest

test :: Monad m => TLT m ()
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

newtype Monad m => M1T m a = M1T { unwrap1 :: IdentityT m a }
runM1T :: Monad m => M1T m a -> m a
runM1T = runIdentityT . unwrap1
newtype Monad m => M2T m a = M2T { unwrap2 :: IdentityT m a }
runM2T :: Monad m => M2T m a -> m a
runM2T = runIdentityT . unwrap2

instance Monad m => Functor (M1T m) where
  fmap f (M1T m) = M1T $ do
    v <- m
    return $ f v
instance Monad m => Applicative (M1T m) where
  pure v = M1T $ pure v
  (M1T m1) <*> (M1T m2) = M1T $ do
    f <- m1
    v <- m2
    return (f v)
instance Monad m => Monad (M1T m) where
  (M1T m) >>= f = M1T $ m >>= (unwrap1 . f)
  (M1T m1) >> (M1T m2) = M1T $ m1 >> m2
  return v = M1T $ return v
instance MonadTrans M1T where lift = M1T . lift

instance Monad m => Functor (M2T m) where
  fmap f (M2T m) = M2T $ do
    v <- m
    return $ f v
instance Monad m => Applicative (M2T m) where
  pure v = M2T $ pure v
  (M2T m1) <*> (M2T m2) = M2T $ do
    f <- m1
    v <- m2
    return (f v)
instance Monad m => Monad (M2T m) where
  (M2T m) >>= f = M2T $ m >>= (unwrap2 . f)
  (M2T m1) >> (M2T m2) = M2T $ m1 >> m2
  return v = M2T $ return v
instance MonadTrans M2T where lift = M2T . lift

instance MonadTLT m n => MonadTLT (M1T m) n where
  liftTLT = lift . liftTLT
instance MonadTLT m n => MonadTLT (M2T m) n where
  liftTLT = lift . liftTLT

ttest = do
  runM1T $ inGroup "M1T tests" $ m1tests
  runM2T $ inGroup "M2T tests" $ m2tests

m1tests = M1T $ do
  "3 is 3 as pure assertion" ~: 3 @==- 3
  "4 is 4 as pure assertion" ~: 4 @==- 4

m2tests = M2T $ do
  "5 is 5 as pure assertion" ~: 5 @==- 5
  "6 is 6 as pure assertion" ~: 6 @==- 6

