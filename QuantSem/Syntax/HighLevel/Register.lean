module

/- These imports make the file happy :) -/
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Data.Complex.Basic

public import QuantSem.Syntax.HighLevel.QuantumTypes

/-
namespace ExplicitRegister

variable (RegTypes : Type 1)

public inductive RegisterShape where
  | bot : RegisterShape /- Empty register, should never appear -/
  | mk (R : RegTypes) : RegisterShape
  | combine (R1 R2 : RegisterShape) : RegisterShape
deriving DecidableEq

notation A "⊗" B => RegisterShape.combine A B

public def Wire (T : RegTypes) : RegisterShape RegTypes := RegisterShape.mk T
public def nWire (n : ℕ) (T : RegTypes) : RegisterShape RegTypes :=
  match n with
  | 0 => RegisterShape.bot
  | 1 => Wire RegTypes T
  | Nat.succ k  => (nWire k T) ⊗ (Wire RegTypes T)

notation "⟨" n "|" m "⟩" => nWire n (Fin m) /- Assumes Fin m is contained within RegTypes -/
-/
/- Bad Idea, don't use ExplicitRegister! -/
/- TODO : Delete -/
/- end ExplicitRegister -/


namespace SyntacticRegister

open QuantumTypes
open Monoid

/-
Quantum registers depend on Quantum Type composition.
Often, the given composition will be the Tensor product of hilbert spaces
-/

public abbrev QuantumRegister := TypeQuantumTypes

public class QuantumRegisterClass extends Monoid TypeQuantumTypes where
  mul := Mul.mul
notation A "⊗ᵣ" B =>  QuantumRegisterClass.mul A B


public abbrev RegisterGetSpace (R : QuantumRegister) := Sigma.fst R
public abbrev RegisterGetStructure (R : QuantumRegister) := Sigma.snd R

@[default_instance]
instance (R : QuantumRegister) : NormedAddCommGroup (RegisterGetSpace R) :=
  (RegisterGetStructure R).toNormedAddCommGroup

@[default_instance]
instance (R : QuantumRegister) : InnerProductSpace ℂ (RegisterGetSpace R) :=
   (RegisterGetStructure R).toInnerProductSpace

@[default_instance]
instance (R : QuantumRegister) : TopologicalSpace (RegisterGetSpace R) :=
  (RegisterGetStructure R).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-
@[default_instance]
instance (M : Type) [AddMonoid M] : Monoid M := _

@[default_instance]
instance (R : QuantumRegister) : Monoid (RegisterGetSpace R) :=
   (RegisterGetStructure R).toInnerProductSpace.to
   toNormedAddCommGroup.toAddCommGroup.toAddGroup.toAddMonoid
-/
end SyntacticRegister
