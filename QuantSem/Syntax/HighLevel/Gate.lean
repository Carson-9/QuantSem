module

public import QuantSem.Syntax.HighLevel.Register
public import QuantSem.Syntax.HighLevel.State

namespace SyntacticGate

open SyntacticRegister
open SyntacticState
open ContinuousLinearMap


@[default_instance]
instance (R : QuantumRegister) : TopologicalSpace (RegisterGetSpace R) :=
  (RegisterGetStructure R).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace


@[expose]
public def QuantumGate (R : QuantumRegister) : Type :=
  unitary ((RegisterGetSpace R) →L[ℂ] (RegisterGetSpace R))
  /- Sigma.fst R -/
  /- unitary (RegisterGetSpace R)   ---> Talk about unitary endomorphisms over (RegisterGetSpace R)-/

/- TODO : Find some other general representation of unitarity.
    Maybe isometries are nice enough in our setting? -/

public abbrev QuantumGateType := Σ R, QuantumGate R

public abbrev QuantumGateGetRegister (G : QuantumGateType) : QuantumRegister := Sigma.fst G
public abbrev QuantumGateGetSpace (G : QuantumGateType) : Type := RegisterGetSpace (Sigma.fst G)


public class QuantumGateAlgebra extends Monoid QuantumGateType where
  mul := Mul.mul
  liftMap {C : QuantumRegisterClass} (G1 G2 : QuantumGateType) :
    (QuantumGateGetSpace (mul G1 G2))
    → QuantumGate ( C.mul (QuantumGateGetRegister G1) (QuantumGateGetRegister G2))

/-
        G(R) ⊗ₘ G(R)
         /\         \
         |            \   ∃!
         |             \/
      R ⊗ᵣ R --------> G(R ⊗ᵣ R)
-/



notation A "⊗ₘ" B => QuantumGateAlgebra.mul A B

end SyntacticGate
