module


public import Qml.SyntaxLevel.HighLevel.Gate

open SyntacticGate
open SyntacticRegister
open SyntacticState

namespace SyntacticCircuit

/- Simple circuits are always representable as unitary matrices, no pesky measurement
    or other quantum operations I'm not aware of -/

public inductive SimpleCircuit : Type where
  | Gate {R} (g : QuantumGate R) : SimpleCircuit
  | HorizontalComp (c1 c2 : SimpleCircuit) : SimpleCircuit
  | VerticalComp (c1 c2 : SimpleCircuit) : SimpleCircuit


public def SimpleCircuitDepth : SimpleCircuit → ℕ :=
  fun
  | SimpleCircuit.Gate _ => 1
  | SimpleCircuit.HorizontalComp c1 c2 => (SimpleCircuitDepth c1) + (SimpleCircuitDepth c2)
  | SimpleCircuit.VerticalComp c1 c2 => Nat.max (SimpleCircuitDepth c1) (SimpleCircuitDepth c2)


public def EvolveState : SimpleCircuit → State → State :=
  fun
  | SimpleCircuit.Gate g =>
  | SimpleCircuit.HorizontalComp c1 c2 => fun s => EvolveState c2 (EvolveState c1 s)
  | SimpleCircuit.VerticalComp c1 c2 =>

end SyntacticCircuit
