module

import Mathlib.Data.Fin.Basic

namespace WhyDoINeedToDoThis

theorem LT_add {n m : ℕ} (h : n < m) : ∀ k, n < m + k := fun
  | 0 => by apply h
  | k' + 1 => let prev := LT_add h k'
              let goalRed := Nat.lt_add_one (m + k')
              Nat.lt_trans prev goalRed

def FinTypeUnion{n : ℕ} {m : ℕ} : Fin (n + m) ≃ (Fin n) ⊕ (Fin m) where
  toFun := fun x => if x < n then (Sum.inl (Fin.mk x _)) else (Sum.inr (Fin.mk x _))
  invFun := fun | Sum.inl y => Fin.mk y (LT_add y.isLt m)
                | Sum.inr z => Fin.mk z (by rw [Nat.add_comm]; apply (LT_add z.isLt n))
  left_inv := _
  right_inv := _

end WhyDoINeedToDoThis
