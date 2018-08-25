%default total

-- Proof by induction on the natural numbers
natInd : (p : Nat -> Type) -> (pz : p 0) -> (ps : (k : Nat) -> p k -> p (S k)) -> (n : Nat) -> p n
natInd p pz ps Z = pz
natInd p pz ps (S k) = ps k $ natInd p pz ps k

plusCommZ : (n : Nat) -> n + 0 = 0 + n
plusCommZ = natInd (\n => n + 0 = 0 + n) Refl (\_ => cong)

plusSLeftS : (n : Nat) -> (m : Nat) -> m + S n = S m + n
plusSLeftS n = natInd (\m => m + S n = S m + n) Refl (\_ => cong)

-- Proof that plus is commutative on the naturals, in terms of natInd
plusComm : (n : Nat) -> (m : Nat) -> n + m = m + n
plusComm n m = natInd (\m => n + m = m + n) (plusCommZ n) (\k => trans (plusSLeftS k n) . cong) m

