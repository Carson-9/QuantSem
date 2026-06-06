module

public import QuantSem.Syntax.HighLevel.Register
public import QuantSem.Syntax.HighLevel.QuantumTypes

open SyntacticRegister QuantumTypes
namespace SyntacticState


@[expose]
public def QuantumStateSpace (R : QuantumRegister) := { x : R.fst // R.snd.toNorm.norm x = 1 }
public abbrev TypeQuantumStates : Type 1 :=
  Σ R : QuantumRegister, QuantumStateSpace R

public class QuantumStateAlgebra extends Monoid TypeQuantumStates where
  mul := Mul.mul
  liftMap {C : QuantumRegisterAlgebra} (s1 s2 : TypeQuantumStates) :
    ((mul s1 s2).fst.fst) → QuantumStateSpace (C.mul (s1.fst) (s2.fst))
  /- Not useful here for now, may have surprises later, but very easily fixable! -/
  /- univPropertyInj : Injective liftMap -/
/-

We may wish to respect the universal property of tensor product : Lifting must
respect the intended injection of decomposable state into the state of register-tensor

     S(R) ⊗ₛ S(R)
         /\         \
         |            \   ∃!
         |             \/
      R ⊗ᵣ R --------> S(R ⊗ᵣ R)


-/

notation A "⊗ₛ" B => QuantumStateAlgebra.mul A B

notation "| " ψ " ⟩" => (ψ : QuantumStateSpace)

/- TODO : Continue denotational stuff.
notation "⟨ " ψ " |" => (ψ†)
-/

end SyntacticState
