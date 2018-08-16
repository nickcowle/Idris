module Data.Seq

import Data.Fin

%access public export

data Seq : Type -> Type where
  Nil : Seq a
  (::) : Lazy a -> Lazy (Seq a) -> Seq a

(++) : Seq a -> Seq a -> Seq a
(++) [] ys = ys
(++) (x :: xs) ys = x :: (Delay $ xs ++ ys)

map : (a -> b) -> Seq a -> Seq b
map f [] = []
map f (x :: xs) = Delay (f x) :: map f xs

concat : Seq $ Seq a -> Seq a
concat [] = []
concat ([] :: xs) = concat xs
concat ((x :: xs) :: xss) = x :: concat (xs :: xss)

range : Int -> Int -> Seq Int
range a b = if a > b then [] else a :: Delay (range (a + 1) b)

filter : (a -> Bool) -> Seq a -> Seq a
filter f [] = []
filter f (x :: xs) = if f x then x :: filter f xs else filter f xs

toList : Seq a -> List a
toList [] = []
toList (x :: xs) = x :: toList xs

head : Seq a -> a
head (x :: xs) = x

fins : (n : Nat) -> Seq $ Fin n
fins Z = []
fins (S k) = FZ :: (map FS $ fins k)

