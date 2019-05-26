{-# LANGUAGE TypeInType, GADTs, TypeFamilies, KindSignatures, ScopedTypeVariables #-}

import Prelude hiding (zip)
import Data.Kind (Type)
infixr :>

data Nat :: Type where
  O :: Nat
  S :: Nat -> Nat

data Vec :: Type -> Nat -> Type where
  Nil  :: (n ~ O) => Vec a n
  (:>) :: (n ~ S m) => a -> Vec a m -> Vec a n

type One = S O

type family Plus (x :: Nat) (y :: Nat) :: Nat where
   Plus O     y = y
   Plus (S x) y = S (Plus x y)

example :: Vec Char (Plus One (Plus One One))
example = 'G' :> 'H' :> 'C' :> Nil


zip :: forall n a b. Vec a n -> Vec b n -> Vec (a,b) n
zip Nil Nil = Nil
zip (x :> xs) (y :> ys) = (x,y) :> zip xs ys

main :: IO ()
main = return ()
