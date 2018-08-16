module SumsTo

%access public export

data SumsTo : Nat -> Nat -> Nat -> Type where
  MkSumsTo : (l : Nat) -> (r : Nat) -> SumsTo l r (l + r)

leftIsSum : SumsTo l Z s -> l = s
leftIsSum (MkSumsTo l Z) = rewrite plusCommutative l 0 in Refl

sumEq : SumsTo l r s -> l + r = s
sumEq (MkSumsTo l r) = Refl

sumSuccLeftSucc : SumsTo l (S r) s -> SumsTo (S l) r s
sumSuccLeftSucc (MkSumsTo l (S r)) = rewrite sym $ plusSuccRightSucc l r in MkSumsTo (S l) r

sumSuccRight : SumsTo l r s -> SumsTo l (S r) (S s)
sumSuccRight (MkSumsTo l r) = rewrite plusSuccRightSucc l r in MkSumsTo l (S r)

