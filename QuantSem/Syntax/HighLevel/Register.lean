/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

/- These imports make the file happy :) -/
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Analysis.InnerProductSpace.Defs

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt


public import QuantSem.Syntax.HighLevel.QuantumTypes

namespace SyntacticRegister

open QuantumTypes
open Monoid
open CategoryTheory

/-
Quantum registers depend on Quantum Type composition.
Often, the given composition will be the Tensor product of hilbert spaces
-/

--public abbrev QuantumRegister := TypeQuantumTypes
public abbrev QuantReg (R : Type) := QuantumTypes.HilbertSpace R
public abbrev TypeQuantumRegister := Σ E, QuantReg E

@[default_instance]
public instance (R : TypeQuantumRegister) : SeminormedAddCommGroup R.fst :=
  R.snd.toSeminormedAddCommGroup

@[expose, coe]
public def QuantRegToTypeQuantumRegister (R : Type) [R' : QuantReg R] :
  TypeQuantumRegister := ⟨R, R'⟩

@[expose, coe, reducible]
public def TypeQuantumRegisterToStructure (R : TypeQuantumRegister) : QuantReg R.fst := R.snd

@[default_instance]
public instance CatRegister : Category TypeQuantumRegister where
  Hom R1 R2 :=  R1.fst →ₗᵢ[ℂ] R2.fst
  id T1 := LinearIsometry.id
  comp f1 f2 := LinearIsometry.comp f2 f1


/-
  Registers can be endowed with the structure of a Monoidal Category
-/

@[expose]
public noncomputable def QuantumRegisterTensor (T1 T2 : TypeQuantumRegister) : TypeQuantumRegister :=
  ⟨TensorProduct ℂ T1.fst T2.fst, @HilbertTensorFun T1.fst T2.fst T1.snd T2.snd ⟩

notation A "⊗ᵣ" B => QuantumRegisterTensor A B

@[expose]
public noncomputable def QuantRegHomTensor {R1 R2 R3 R4 : TypeQuantumRegister}
  (f : R1 ⟶ R3) (g : R2 ⟶ R4) :
  QuantumRegisterTensor R1 R2 ⟶ QuantumRegisterTensor R3 R4 :=
  @TensorLinearIsometries R1.fst R2.fst R3.fst  R4.fst R1.snd R2.snd R3.snd R4.snd
    (f : R1.fst →ₗᵢ[ℂ] R3.fst) g

@[expose]
public noncomputable def QuantRegHomTensorAssoc (R1 R2 R3 : TypeQuantumRegister) :
  ((R1 ⊗ᵣ R2) ⊗ᵣ R3) ≅ (R1 ⊗ᵣ (R2 ⊗ᵣ R3)) :=
  Iso.mk
    (existingIso.toLinearIsometry)
    (existingIso.symm.toLinearIsometry)
    (by sorry)  -- leftInverse is not strictly the same...
    (by sorry) where
  existingIso := @HilbertTensorAssoc R1.fst R2.fst R3.fst R1.snd R2.snd R3.snd

@[expose]
public noncomputable def CLeftUnitor (R : TypeQuantumRegister) :
  (⟨ℂ, CIsHilbert⟩ ⊗ᵣ R) ≅ R :=
  Iso.mk
    (existingIso.toLinearIsometry)
    (existingIso.symm.toLinearIsometry)
    (by sorry)
    (by sorry) where
    existingIso := @CIsLeftNeutral R.fst R.snd

@[expose]
public noncomputable def CRightUnitor (R : TypeQuantumRegister) :
  (R ⊗ᵣ ⟨ℂ, CIsHilbert⟩) ≅ R :=
  Iso.mk
    (existingIso.toLinearIsometry)
    (existingIso.symm.toLinearIsometry)
    (by sorry)
    (by sorry) where
    existingIso := @CIsRightNeutral R.fst R.snd

public theorem id_tensor_id : ∀ X Y,
  QuantRegHomTensor (@IdMap X.fst X.snd) (@IdMap Y.fst Y.snd) = @IdMap (X ⊗ᵣ Y).fst (X ⊗ᵣ Y).snd :=
  by intro X Y; apply @TensorOfIdIsId X.fst Y.fst X.snd Y.snd


@[default_instance]
public instance MonCatRegister : MonoidalCategory TypeQuantumRegister where
  tensorObj := QuantumRegisterTensor
  whiskerLeft X Y1 Y2 f := QuantRegHomTensor LinearIsometry.id f
  whiskerRight f Y := QuantRegHomTensor f LinearIsometry.id
  tensorUnit := ⟨ℂ, CIsHilbert⟩
  associator X Y Z := QuantRegHomTensorAssoc X Y Z
  leftUnitor X := CLeftUnitor X
  rightUnitor X := CRightUnitor X


public noncomputable def QuantumRegister.MulTensor
  (famReg : List TypeQuantumRegister) (buffer : TypeQuantumRegister) (fstRound : Bool) :=
  match famReg with
  | [] => buffer
  | h :: t => if fstRound then QuantumRegister.MulTensor t h false
                          else QuantumRegister.MulTensor t (buffer ⊗ᵣ h) false

notation "⨂ᵣ" l => QuantumRegister.MulTensor l 𝟙 true


/-
  Prove that the norm is expressed with the inner product
-/
public theorem NormFromInner (R : Type) [R' : QuantReg R] (z : R) :
  ‖z‖ = √ (Complex.re (R'.inner z z)) :=
  by calc
    ‖z‖ = √(‖z‖ ^ 2)                    := by symm; simp;
    _   = √(Complex.re (R'.inner z z))  := by rw[R'.norm_sq_eq_re_inner]; rfl



end SyntacticRegister
