module

public import QuantSem.Syntax.HighLevel.Register
public import QuantSem.Syntax.HighLevel.State

open SyntacticRegister
open SyntacticState
open ContinuousLinearMap

/- Lean shenanigans as it cannot easily produce the required default instances -/
section test
namespace SyntacticGate
variable (R : QuantumRegister)

@[default_instance]
instance : SeminormedAddCommGroup R.fst :=
  R.snd.toSeminormedAddCommGroup

public def QuantumGate : Type := (R.fst →ₗᵢ[ℂ] R.fst)
end SyntacticGate
end test

section
namespace SyntacticGate
public abbrev TypeQuantumGate := Σ R : QuantumRegister, QuantumGate R

public class QuantumGateAlgebra extends Monoid TypeQuantumGate where
  mul := Mul.mul
  liftMap {C : QuantumRegisterAlgebra} (G1 G2 : TypeQuantumGate) :
    ((mul G1 G2).fst.fst) → QuantumGate ( C.mul (G1.fst) (G2.fst))

/-
        G(R) ⊗ₘ G(R)
         /\         \
         |            \   ∃!
         |             \/
      R ⊗ᵣ R --------> G(R ⊗ᵣ R)
-/



notation A "⊗ₘ" B => QuantumGateAlgebra.mul A B

end SyntacticGate
end
