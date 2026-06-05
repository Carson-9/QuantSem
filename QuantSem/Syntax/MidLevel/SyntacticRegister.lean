module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Data.Complex.Basic

namespace SyntacticQubitRegister

open Complex

@[ext]
public structure Register (n : ℕ) where
  mk ::
  WireType : Fin n → ℕ

deriving DecidableEq

@[ext]
lemma Qml.Register_of_fun {n : ℕ} (R1 R2 : Register n)
  (hyp : ∀ i : Fin n, R1.WireType i = R2.WireType i)
  : R1 = R2 := by ext; apply hyp

lemma Qml.Register_from_fun {n : ℕ} (R1 R2 : Register n) (hyp : R1 = R2)
  : R1.WireType = R2.WireType :=
  by rw [hyp]

def RegIsomFin {n : ℕ} : Register n ≃ (Fin n → ℕ) where
  toFun R := R.WireType
  invFun := Register.mk
  left_inv R := by rfl
  right_inv V := by rfl

/- Isomorphism to List.Vectors (Mathematics-sided Vector structure) -/

public def RegisterFromVec {n : ℕ} (l : List.Vector ℕ n) : Register n :=
  Register.mk (fun i => l.get i)

public def RegisterFromVec' {n : ℕ} (l : Vector ℕ n) : Register n :=
  Register.mk (fun i => l.get i)

lemma RegVecAtIndex {n : ℕ} (l : List.Vector ℕ n) (i : Fin n) :
  (RegisterFromVec l).WireType i = List.Vector.get l i :=
  by rfl

def RegisterToVec {n : ℕ} (R : Register n) : List.Vector ℕ n :=
  List.Vector.ofFn R.WireType

def RegisterToVec' {n : ℕ} (R : Register n) : Vector ℕ n :=
  Vector.ofFn R.WireType

def RegisterIsomVec {n : ℕ} : Register n ≃ List.Vector ℕ n :=
  Equiv.trans RegIsomFin (Equiv.symm (Equiv.vectorEquivFin ℕ n))


/- A notation to simply describe a register signature -/
notation "Reg" vecShape => RegisterFromVec' (Vector.mk (Array.mk ↑vecShape) (by rfl))

public def RegisterTensor {n : ℕ} {m : ℕ} (R1 : Register n) (R2 : Register m) : Register (n + m) :=
  RegisterFromVec' (Vector.append (RegisterToVec' R1) (RegisterToVec' R2))

end SyntacticQubitRegister
