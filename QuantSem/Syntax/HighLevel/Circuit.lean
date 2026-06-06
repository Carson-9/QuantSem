module


public import QuantSem.Syntax.HighLevel.Gate

open SyntacticGate
open SyntacticRegister
open SyntacticState

namespace SyntacticCircuit

variable {C : QuantumRegisterAlgebra} {S : QuantumStateAlgebra} {G : QuantumGateAlgebra}

/- Simple circuits are always representable as unitary matrices, no pesky measurement
    or other quantum operations I'm not aware of -/

public inductive SimpleCircuitOverRegister (R : QuantumRegister) where
  | Gate (g : QuantumGate R)
  | HorizontalComp (c1 c2 : SimpleCircuitOverRegister R)

public abbrev TypeSimpleCircuit := Σ R : QuantumRegister, SimpleCircuitOverRegister R

public class SimpleCircuitAlgebra extends Monoid TypeSimpleCircuit where
  mul := Mul.mul
  liftMap (c1 c2 : TypeSimpleCircuit) :
    ((mul c1 c2).fst.fst) → SimpleCircuitOverRegister (C.mul (c1.fst) (c2.fst))
  /- univPropertyInj : Injective liftMap -/
/-
     C(R) ⊗ₖ C(R)
         /\         \
         |            \   ∃!
         |             \/
      R ⊗ₖ R --------> C(R ⊗ₖ R)

  Intuition : Composed circuits are a subclass of circuits over the composed space
-/

notation A "⊗ₖ" B =>  SimpleCircuitAlgebra.mul A B

variable {R : QuantumRegister}

public def SimpleCircuitDepth (c : SimpleCircuitOverRegister R) : ℕ :=
  match c with
  | SimpleCircuitOverRegister.Gate _ => 1
  | SimpleCircuitOverRegister.HorizontalComp c1 c2 =>
    (SimpleCircuitDepth c1) + (SimpleCircuitDepth c2)


public def SimpleCircuitGateCount (c : SimpleCircuitOverRegister R) : ℕ :=
  match c with
  | SimpleCircuitOverRegister.Gate _ => 1
  | SimpleCircuitOverRegister.HorizontalComp c1 c2 =>
    (SimpleCircuitDepth c1) + (SimpleCircuitDepth c2)

public def SimpleCircuitGetShape :
  SimpleCircuitOverRegister R → QuantumRegister := fun _ => R

public def EvolveState (c : SimpleCircuitOverRegister R)
  (s : QuantumStateSpace R) :
  QuantumStateSpace R :=
  match c with
  | SimpleCircuitOverRegister.Gate g => (LinearIsometry.toLinearMap g) s
  | SimpleCircuitOverRegister.HorizontalComp c1 c2 => EvolveState c2 (EvolveState c1 s)

end SyntacticCircuit
