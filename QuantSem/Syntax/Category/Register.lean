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


public import QuantSem.Syntax.Category.QuantumTypes

namespace SyntacticRegister

open QuantumTypes
open Monoid
open CategoryTheory
open InnerProductSpace
open InnerProductSpace.Core

/-
Quantum registers depend on Quantum Type composition.
Often, the given composition will be the Tensor product of hilbert spaces
-/

--public abbrev QuantumRegister := TypeQuantumTypes
public abbrev QuantReg (R : Type) := QuantumTypes.HilbertSpace R
public abbrev TypeQuantumRegister := Σ E, QuantReg E

public abbrev TypeQuantumRegister.space (R : TypeQuantumRegister) := R.fst
public abbrev TypeQuantumRegister.struct (R : TypeQuantumRegister) := R.snd

@[default_instance]
public instance (R : TypeQuantumRegister) : SeminormedAddCommGroup R.fst :=
  R.snd.toSeminormedAddCommGroup

@[default_instance]
public instance (R : TypeQuantumRegister) : HilbertSpace R.fst :=
  R.snd

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
    Normalize vectors.
-/

public noncomputable abbrev NormalizeElement {R1 : TypeQuantumRegister} (x : R1.space) : R1.space :=
  ‖x‖⁻¹ • x

public theorem ElementIsUnitAndSize  {R1 : TypeQuantumRegister} (x : R1.space) :
  ‖x‖ ≠ 0 → x = ‖x‖ • (NormalizeElement x) := by intro h; unfold NormalizeElement; rw[<- mul_smul, Field.mul_inv_cancel ‖x‖]; simp; apply h

public theorem NormOfNormalizedIsOne {R1 : TypeQuantumRegister} (x : R1.space) :
  ‖x‖ ≠ 0 → ‖(NormalizeElement x)‖ = 1 := by intro hX; unfold NormalizeElement; rw[norm_smul]; simp; rw[mul_comm, Field.mul_inv_cancel ‖x‖]; apply hX

public theorem NormZeroIffZero {R1 : TypeQuantumRegister} :
  ∀ x : R1.space, ‖x‖ = 0 ↔ x = 0 := by intro x; apply Iff.trans (normSqZero x) (innerZero x) where
    normSqZero : ∀ x : R1.space, ‖x‖ = 0 ↔ (R1.struct.inner x x).re = 0 := by intro x; rw[NormFromInner]; simp; apply Real.sqrt_eq_zero; rw[<- Complex.ofReal_pow, Complex.ofReal_re]; apply Even.pow_nonneg; simp
    normSqExpr : ∀ x : R1.space, (R1.struct.inner x x).re = 0 ↔ R1.struct.inner x x = 0 := by intro x; apply Iff.intro; intro hX; apply Complex.ext; rw[hX]; simp; simp; rw[<- Complex.ofReal_pow, Complex.ofReal_im]; intro h; rw[h]; simp
    innerZero : ∀ x : R1.space, (R1.struct.inner x x).re = 0 ↔ x = 0 := by intro x; apply Iff.trans (normSqExpr x) (inner_self_eq_zero)


@[ext]
public theorem CatRegisterHomExt {R1 R2 : TypeQuantumRegister} (f g : R1 ⟶ R2) :
  (∀ x : R1.space, f.toFun x = g.toFun x) → f = g :=
  by intro h; apply LinearIsometry.ext_iff.mpr; apply h

public theorem CatRegisterHomExtIff {R1 R2 : TypeQuantumRegister} (f g : R1 ⟶ R2) :
  f = g ↔ (∀ x : R1.space, f.toFun x = g.toFun x) :=
  by apply Iff.intro; intro hEq; rw[hEq]; intro x; rfl; apply CatRegisterHomExt

/-
  Registers can be endowed with the structure of a Monoidal Category
-/


@[expose]
public noncomputable def QuantumRegisterTensor (T1 T2 : TypeQuantumRegister) : TypeQuantumRegister :=
  ⟨TensorProduct ℂ T1.fst T2.fst, @HilbertTensorFun T1.fst T2.fst T1.snd T2.snd ⟩

notation A "⊗ᵣ" B => QuantumRegisterTensor A B

@[simp]
public theorem SpaceCommutesWithTensor (R1 R2 : TypeQuantumRegister) :
  (R1 ⊗ᵣ R2).space = TensorProduct ℂ R1.space R2.space := by rfl

/-
    Elements of a Tensor can always be written as a sum of separables
-/

public def StatesAsCombinationOfSeparables {R1 R2 : TypeQuantumRegister} :
  (R1 ⊗ᵣ R2).space ≃
    Submodule.span ℂ {t : TensorProduct ℂ R1.space R2.space | ∃ (m : R1.space) (n : R2.space), m ⊗ₜ[ℂ] n = t} :=
    .mk (fun x => ⟨x, by rw[TensorProduct.span_tmul_eq_top ℂ R1.space R2.space]; simp⟩) (fun a => a.val)
    (by unfold Function.LeftInverse; intro x; simp)
    (by unfold Function.RightInverse; intro x; simp)

public def SepToRegTensorProp {R1 R2 : TypeQuantumRegister}
  (p : (x : TensorProduct ℂ R1.space R2.space) → (x ∈ Submodule.span ℂ {t : TensorProduct ℂ R1.space R2.space | ∃ (m : R1.space) (n : R2.space), m ⊗ₜ[ℂ] n = t}) → Prop)
  : (R1 ⊗ᵣ R2).space → Prop :=
  fun x => p (StatesAsCombinationOfSeparables x) (StatesAsCombinationOfSeparables x).prop

public def RegTensorToSepProp {R1 R2 : TypeQuantumRegister}
  (p : (R1 ⊗ᵣ R2).space → Prop) :
  (x : TensorProduct ℂ R1.space R2.space) → (x ∈ Submodule.span ℂ {t : TensorProduct ℂ R1.space R2.space | ∃ (m : R1.space) (n : R2.space), m ⊗ₜ[ℂ] n = t}) → Prop :=
  fun x hx => p (StatesAsCombinationOfSeparables.symm (Subtype.mk x hx))

public theorem SeparablePropCoherence {R1 R2 : TypeQuantumRegister}  (p : (R1 ⊗ᵣ R2).space → Prop) :
   ∀ x, (p x) ↔ ((RegTensorToSepProp p) (StatesAsCombinationOfSeparables x).val (StatesAsCombinationOfSeparables x).prop)
  := by intro x; rfl

public theorem RegisterInduction {R1 R2 : TypeQuantumRegister}
  (property : (R1 ⊗ᵣ R2).space → Prop)
  (hzero : property 0)
  (hAllBasis : ∀ x1 : R1.space, ∀ x2 : R2.space, property (x1 ⊗ₜ[ℂ] x2))
  (hLinear : ∀ x1 x2 : ((R1 ⊗ᵣ R2).space), property x1 → property x2 → property (x1 + x2))
  (hmul :  ∀ x : ((R1 ⊗ᵣ R2).space), ∀ c : ℂ, property x → property (c • x)) :
  ∀ x : ((R1 ⊗ᵣ R2).space), property x :=
  by intro x; apply
   (
    Submodule.span_induction (p := (RegTensorToSepProp property))
    (fun x hx => (SeparablePropCoherence property x).mp (by
      have hab : ∃ a b, a ⊗ₜ[ℂ] b = x := hx.out
      rcases hab with ⟨a, b, hfin⟩; rw[<- hfin]; apply hAllBasis a b))
    ((SeparablePropCoherence property 0).mp hzero)
    (fun x y hx hy wx wy => (SeparablePropCoherence property (x + y)).mp (hLinear x y ((SeparablePropCoherence property x).mpr wx) ((SeparablePropCoherence property y).mpr wy)))
    (fun a x hx wx => (SeparablePropCoherence property (a • x)).mp (hmul x a ((SeparablePropCoherence property x).mp wx)))
  ); apply (StatesAsCombinationOfSeparables x).prop


@[expose]
public noncomputable def QuantRegHomTensor {R1 R2 R3 R4 : TypeQuantumRegister}
  (f : R1 ⟶ R3) (g : R2 ⟶ R4) :
  QuantumRegisterTensor R1 R2 ⟶ QuantumRegisterTensor R3 R4 :=
  @TensorLinearIsometries R1.fst R2.fst R3.fst  R4.fst R1.snd R2.snd R3.snd R4.snd
    (f : R1.fst →ₗᵢ[ℂ] R3.fst) g

notation f "⊗ₕ" g => QuantRegHomTensor f g


@[simp]
public theorem arrow_is_comp {R1 R2 R3 : TypeQuantumRegister} (f : R1 ⟶ R2) (g : R2 ⟶ R3)
  : (f ≫ g) = (LinearIsometry.comp g f) := by rfl

@[expose]
public def id_map (R : TypeQuantumRegister) : R ⟶ R := @IdMap R.fst R.snd

@[simp]
public theorem id_map_is_neutral_left {R1 R2 : TypeQuantumRegister}
  (f : R1 ⟶ R2) : id_map R1 ≫ f = f := by rfl

@[simp]
public theorem id_map_is_neutral_right {R1 R2 : TypeQuantumRegister}
  (f : R1 ⟶ R2) : f ≫ id_map R2 = f := by rfl

@[simp]
public theorem id_tensor_id : ∀ X Y,
  QuantRegHomTensor (@IdMap X.fst X.snd) (@IdMap Y.fst Y.snd) = @IdMap (X ⊗ᵣ Y).fst (X ⊗ᵣ Y).snd :=
  by intro X Y; apply @TensorOfIdIsId X.fst Y.fst X.snd Y.snd

@[simp]
public theorem one_is_id : ∀ X : TypeQuantumRegister, 𝟙 X = @IdMap X.fst X.snd :=
  by intro X; rfl

@[simp]
public theorem tensor_factorises : ∀ A A' C B B' D, ∀ (f : A' ⟶ C) (g : B' ⟶ D)
  (h : A ⟶ A') (i : B ⟶ B'),
  (QuantRegHomTensor h i) ≫ (QuantRegHomTensor f g) = QuantRegHomTensor (h ≫ f) (i ≫ g) :=
  by intro A A' B B' C D f g h i; apply @TensorFactorises A.fst A'.fst B.fst B'.fst C.fst D.fst A.snd A'.snd B.snd B'.snd C.snd D.snd f g h i

@[simp]
public theorem id_is_neutral_left : ∀ A B : TypeQuantumRegister, ∀ (f : A ⟶ B),
  f ≫ (@IdMap B.fst B.snd) = f := by intro A B f; apply (@IdIsNeutralLeft A.fst B.fst A.snd B.snd f)

@[simp]
public theorem id_is_neutral_right : ∀ A B : TypeQuantumRegister, ∀ (f : A ⟶ B),
  (@IdMap A.fst A.snd) ≫ f = f := by intro A B f; apply (@IdIsNeutralRight A.fst B.fst A.snd B.snd f)


@[expose]
public noncomputable def QuantRegHomTensorAssoc (R1 R2 R3 : TypeQuantumRegister) :
  ((R1 ⊗ᵣ R2) ⊗ᵣ R3) ≅ (R1 ⊗ᵣ (R2 ⊗ᵣ R3)) :=
  Iso.mk
    (existingIso.toLinearIsometry)
    (existingIso.symm.toLinearIsometry)
    (by rw[one_is_id]; unfold CategoryStruct.comp; unfold CatRegister; simp; apply (EquivalenceToIsometryOfSymmRight existingIso))
    (by rw[one_is_id]; unfold CategoryStruct.comp; unfold CatRegister; simp; apply (EquivalenceToIsometryOfSymmLeft existingIso))
    where existingIso := @HilbertTensorAssoc R1.fst R2.fst R3.fst R1.snd R2.snd R3.snd


@[expose]
public noncomputable def CLeftUnitor (R : TypeQuantumRegister) :
  (⟨ℂ, CIsHilbert⟩ ⊗ᵣ R) ≅ R :=
  Iso.mk
    (existingIso.toLinearIsometry)
    (existingIso.symm.toLinearIsometry)
    (by rw[one_is_id]; unfold CategoryStruct.comp; unfold CatRegister; simp; apply (EquivalenceToIsometryOfSymmRight existingIso))
    (by rw[one_is_id]; unfold CategoryStruct.comp; unfold CatRegister; simp; apply (EquivalenceToIsometryOfSymmLeft existingIso))
    where existingIso := @CIsLeftNeutral R.fst R.snd

@[expose]
public noncomputable def CRightUnitor (R : TypeQuantumRegister) :
  (R ⊗ᵣ ⟨ℂ, CIsHilbert⟩) ≅ R :=
  Iso.mk
    (existingIso.toLinearIsometry)
    (existingIso.symm.toLinearIsometry)
    (by rw[one_is_id]; unfold CategoryStruct.comp; unfold CatRegister; simp; apply (EquivalenceToIsometryOfSymmRight existingIso))
    (by rw[one_is_id]; unfold CategoryStruct.comp; unfold CatRegister; simp; apply (EquivalenceToIsometryOfSymmLeft existingIso))
    where existingIso := @CIsRightNeutral R.fst R.snd

public theorem AssocNaturality {R1 R2 R3 R4 R5 R6 : TypeQuantumRegister}
  (f : R1 ⟶ R4) (g : R2 ⟶ R5) (h : R3 ⟶ R6) :
  (((f ⊗ₕ g) ⊗ₕ h) ≫ (QuantRegHomTensorAssoc R4 R5 R6).hom) =
  ((QuantRegHomTensorAssoc R1 R2 R3).hom ≫ ((f ⊗ₕ (g ⊗ₕ h)))) :=
  by
    unfold QuantRegHomTensorAssoc QuantRegHomTensorAssoc.existingIso QuantumRegisterTensor
    unfold QuantRegHomTensor
    simp


@[default_instance]
public noncomputable instance MonCatRegister : MonoidalCategory TypeQuantumRegister where
  tensorObj := QuantumRegisterTensor
  whiskerLeft X Y1 Y2 f := QuantRegHomTensor LinearIsometry.id f
  whiskerRight f Y := QuantRegHomTensor f LinearIsometry.id
  tensorUnit := ⟨ℂ, CIsHilbert⟩
  associator X Y Z := QuantRegHomTensorAssoc X Y Z
  leftUnitor X := CLeftUnitor X
  rightUnitor X := CRightUnitor X
  id_tensorHom_id := by intro X Y; simp;
  tensorHom_comp_tensorHom := by
    intro X1 X2 Y1 Y2 Z1 Z2 f g h i; rw[tensor_factorises, tensor_factorises, id_is_neutral_left, id_is_neutral_left, id_is_neutral_right, id_is_neutral_right, tensor_factorises, tensor_factorises, id_is_neutral_left, id_is_neutral_right];
  whiskerLeft_id := by intro X Y; rw[one_is_id, id_tensor_id]; rfl
  id_whiskerRight := by intro X Y; rw[one_is_id, id_tensor_id]; rfl
  associator_naturality := by intro X1 X2 X3 Y1 Y2 Y3 f1 f2 f3; simp; ext x; unfold QuantRegHomTensorAssoc; unfold QuantRegHomTensorAssoc.existingIso; simp; sorry--rw[TensorAssocOverComp]
  leftUnitor_naturality := by intro X Y f; unfold CLeftUnitor; simp; sorry
  rightUnitor_naturality := by intro X Y f; ext x; simp; sorry
  triangle := by intro X Y; ext x; simp; sorry
  pentagon := by sorry



public noncomputable def QuantumRegister.MulTensor
  (famReg : List TypeQuantumRegister) (buffer : TypeQuantumRegister) (fstRound : Bool) :=
  match famReg with
  | [] => buffer
  | h :: t => if fstRound then QuantumRegister.MulTensor t h false
                          else QuantumRegister.MulTensor t (buffer ⊗ᵣ h) false

notation "⨂ᵣ" l => QuantumRegister.MulTensor l MonCatRegister.tensorUnit true


end SyntacticRegister
