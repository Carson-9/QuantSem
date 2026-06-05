module

public import Qml.SyntacticQubitCircuit.SyntacticRegister
public import Qml.SyntacticQubitCircuit.SyntacticState

namespace SyntacticQubitGate

open SyntacticQubitRegister
open SyntacticQubitState

public structure Gate {n : ℕ} (R : Register n) where
  mk ::
  StateUpdate : State R → State R


public def MatrixForm {n : ℕ} {R : Register n} (StateUpdate : State R → State R)
  : Fin (TensorDimension R) → Fin (TensorDimension R) → ℂ :=
  fun i j => (StateUpdate (basisState R i)).superposition j

end SyntacticQubitGate
