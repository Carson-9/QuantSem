module

public import QuantSem.Syntax.HighLevel.Register
open SyntacticRegister

namespace SyntacticState

@[expose]
public def QuantumStateSpace (R : QuantumRegister) : Type := Sigma.fst R
public abbrev QuantumStateType := Σ R, QuantumStateSpace R


public abbrev QuantumStateGetRegister (S : QuantumStateType) : QuantumRegister := Sigma.fst S
public abbrev QuantumStateGetSpace (S : QuantumStateType) : Type := RegisterGetSpace (Sigma.fst S)

public class QuantumStateAlgebra extends Monoid QuantumStateType where
  mul := Mul.mul
  liftMap {C : QuantumRegisterClass} (S1 S2 : QuantumStateType) :
    (QuantumStateGetSpace (mul S1 S2))
    → QuantumStateSpace ( C.mul (QuantumStateGetRegister S1) (QuantumStateGetRegister S2))
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
