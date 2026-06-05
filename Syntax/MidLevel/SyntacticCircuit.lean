module


public import Qml.SyntacticQubitCircuit.SyntacticGate

namespace SyntacticQubitCircuit

open SyntacticQubitGate
open SyntacticQubitRegister

inductive SimpleCircuit {n : ℕ} (R : Register n) : Type where
  | GateCons (g : Gate R) : SimpleCircuit R
  | HorizontalComp (c1 c2 : SimpleCircuit R) : SimpleCircuit R
  | VerticalComp {a b} {R1 : Register a} {R2 : Register b}
    (c1 : SimpleCircuit R1) (c2 : SimpleCircuit R2)
    : SimpleCircuit (a + b) (RegisterTensor R1 R2)


def SimpleCircuitDepth {GateType : Nat → Type} {n : Nat} : SimpleCircuit GateType n → Nat :=
  fun
  | SimpleCircuit.GateCons _ => 1
  | SimpleCircuit.HorizontalComp c1 c2 => (SimpleCircuitDepth c1) + (SimpleCircuitDepth c2)
  | SimpleCircuit.VerticalComp c1 c2 => Nat.max (SimpleCircuitDepth c1) (SimpleCircuitDepth c2)

end SyntacticQubitCircuit
