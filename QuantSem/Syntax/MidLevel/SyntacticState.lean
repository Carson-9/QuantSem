module


public import Mathlib.Analysis.InnerProductSpace.Basic
public import Qml.SyntacticQubitCircuit.SyntacticRegister

namespace SyntacticQubitState
open SyntacticQubitRegister


public def TensorDimension {n : ℕ} (R : Register n) : ℕ :=
  (∏ i : Fin n, R.WireType i)

/- Entanglement destroys factorizable maps -/
@[expose]
public def RegisterTensorType {n : ℕ} (R : Register n) : Type :=
  Fin (TensorDimension R)
deriving DecidableEq

public structure State {n : Nat} (R : Register n) where
  mk ::
  superposition : RegisterTensorType R → ℂ

@[expose]
public def basisState {n : ℕ} (R : Register n) (i : RegisterTensorType R) : State R :=
  State.mk (fun j => if i = j then (1 : ℂ) else 0)

/- Todo : Finish -/
/-
@[expose]
public def TensorState {n m: ℕ} {R1 : Register n} {R2 : Register m}
  (s1 : State R1) (s2 : State R2) : State (RegisterTensor R1 R2) :=
  State.mk (fun i : RegisterTensorType (RegisterTensor R1 R2) =>
              (s1.superposition (Fin.mk (i.val % TensorDimension R1) (Nat.mod_lt i.val (by )) )) *
              (s2.superposition (Fin.mk (Nat.div i.val (TensorDimension R2)) _ )))
-/
end SyntacticQubitState
