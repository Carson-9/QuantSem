/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

/- These imports make the file happy :) -/
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt


public import QuantSem.Syntax.HighLevelInstance.QuantumTypes

namespace SyntacticRegister

open QuantumTypes
open Monoid
open LinearIsometry

/-
Quantum registers depend on Quantum Type composition.
Often, the given composition will be the Tensor product of hilbert spaces
-/

--public abbrev QuantumRegister := TypeQuantumTypes
public class QuantReg (R : Type) extends HilbertSpace R where
  innerFun := toInnerProductSpace.inner

public abbrev TypeQuantumRegister := Σ E, QuantReg E

@[expose, coe]
public def QuantRegToTypeQuantumRegister (R : Type) [R' : QuantReg R] :
  TypeQuantumRegister := ⟨R, R'⟩

@[expose, coe, reducible]
public def TypeQuantumRegisterToStructure (R : TypeQuantumRegister) : QuantReg R.fst := R.snd

public class QuantumRegisterAlgebra extends Monoid TypeQuantumRegister where
  mulFun := toSemigroup.toMul.mul


notation A "⊗ᵣ" B =>  QuantumRegisterAlgebra.mulFun A B

public def QuantumRegister.MulTensor {C : QuantumRegisterAlgebra}
  (famReg : List TypeQuantumRegister) (buffer : TypeQuantumRegister) (fstRound : Bool) :=
  match famReg with
  | [] => buffer
  | h :: t => if fstRound then @QuantumRegister.MulTensor C t h false
                          else @QuantumRegister.MulTensor C t (C.mul buffer h) false

notation "⨂ᵣ" l => QuantumRegister.MulTensor l QuantumRegisterAlgebra.one true


/-
  Prove that the norm is expressed with the inner product
-/

public theorem NormFromInner (R : Type) [R' : QuantReg R] (z : R) :
  ‖z‖ = √ (Complex.re (R'.inner z z)) :=
  by calc
    ‖z‖ = √(‖z‖ ^ 2) := by symm; simp;
    _ = √(Complex.re (R'.inner z z)) := by rw[R'.norm_sq_eq_re_inner]; rfl



end SyntacticRegister
