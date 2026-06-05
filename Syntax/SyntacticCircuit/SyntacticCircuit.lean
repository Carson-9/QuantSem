/-
module


public import Qml.SyntacticCircuit.SyntacticGate

namespace SyntacticCircuit
section Definition

open SyntacticGate

inductive SimpleCircuit (GateType : Nat → Type) : (n : Nat) → Type where
  | GateCons {n} (g : (GateType n)) : SimpleCircuit GateType n
  | HorizontalComp {n} (c1 : SimpleCircuit GateType n) (c2 : SimpleCircuit GateType n) : SimpleCircuit GateType n
  | VerticalComp {a b} (c1 : SimpleCircuit GateType a) (c2 : SimpleCircuit GateType b) : SimpleCircuit GateType (a + b)


def SimpleCircuitDepth {GateType : Nat → Type} {n : Nat} : SimpleCircuit GateType n → Nat :=
  fun
  | SimpleCircuit.GateCons k => 1
  | SimpleCircuit.HorizontalComp c1 c2 => (SimpleCircuitDepth c1) + (SimpleCircuitDepth c2)
  | SimpleCircuit.VerticalComp c1 c2 => Nat.max (SimpleCircuitDepth c1) (SimpleCircuitDepth c2)

-/
