module

/- These imports make the file happy :) -/
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Data.Complex.Basic

public import QuantSem.Syntax.HighLevel.QuantumTypes

namespace SyntacticRegister

open QuantumTypes
open Monoid

/-
Quantum registers depend on Quantum Type composition.
Often, the given composition will be the Tensor product of hilbert spaces
-/

public abbrev QuantumRegister := TypeQuantumTypes

public class QuantumRegisterAlgebra extends Monoid TypeQuantumTypes where
  mul := Mul.mul
notation A "⊗ᵣ" B =>  QuantumRegisterAlgebra.mul A B

/-
public abbrev RegisterSpace (R : QuantumRegister) := Sigma.fst R
public abbrev RegisterStructure (R : QuantumRegister) := Sigma.snd R


@[default_instance 100]
instance RegNormAddCommGroup (R : QuantumRegister) : NormedAddCommGroup (RegisterSpace R) :=
  (RegisterStructure R).toNormedAddCommGroup

@[default_instance 100]
instance RegNorm (R : QuantumRegister) : Norm (RegisterSpace R) :=
  (RegisterStructure R).toNorm

@[default_instance 100]
instance RegInnerProductSpace (R : QuantumRegister) : InnerProductSpace ℂ (RegisterSpace R) :=
   (RegisterStructure R).toInnerProductSpace

@[default_instance 100]
instance RegTopologicalSpace (R : QuantumRegister) : TopologicalSpace (RegisterSpace R) :=
  (RegisterStructure R).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
-/
/-
@[default_instance]
instance (M : Type) [AddMonoid M] : Monoid M := _

@[default_instance]
instance (R : QuantumRegister) : Monoid (RegisterSpace R) :=
   (RegisterStructure R).toInnerProductSpace.to
   toNormedAddCommGroup.toAddCommGroup.toAddGroup.toAddMonoid
-/
end SyntacticRegister
