/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module


public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm

open ContinuousLinearMap InnerProductSpace
open scoped InnerProduct ComplexInnerProductSpace

namespace QuantumTypes

-- Make Hilbert spaces into a Class rather than a Structure. We wish for a type to have
-- a Hilbert space structure
public class HilbertSpace (E : Type) extends NormedAddCommGroup E,
  InnerProductSpace ℂ E, CompleteSpace E

variable {E F G H : Type} [EH : HilbertSpace E] [HilbertSpace F] [HilbertSpace G] [HilbertSpace H]

/-
    Hilbert spaces can be composed with the Tensor product
-/

@[default_instance]
public noncomputable instance HilbertTensor : HilbertSpace (TensorProduct ℂ E F) where
  complete := by intro f cauchy_f; sorry -- known todo of mathlib

public noncomputable abbrev HilbertTensorFun (E F : Type) [HilbertSpace E] [HilbertSpace F]
  : HilbertSpace (TensorProduct ℂ E F) := HilbertTensor

public noncomputable abbrev HilbertTensorAssoc :
  TensorProduct ℂ (TensorProduct ℂ E F) G ≃ₗᵢ[ℂ]
  TensorProduct ℂ E (TensorProduct ℂ F G) :=
  TensorProduct.assocIsometry ℂ E F G

/-
    ℂ is the unit of the tensor product. It is a Hilbert space
-/

@[default_instance]
public noncomputable instance CHilbert : HilbertSpace ℂ where
@[expose, implicit_reducible]
public noncomputable def CIsHilbert : HilbertSpace ℂ := CHilbert

public noncomputable abbrev CIsLeftNeutral :
  TensorProduct ℂ ℂ E ≃ₗᵢ[ℂ] E := TensorProduct.lidIsometry ℂ E

public noncomputable abbrev CIsRightNeutral :
  TensorProduct ℂ E ℂ ≃ₗᵢ[ℂ] E :=
  LinearIsometryEquiv.trans (TensorProduct.commIsometry ℂ E ℂ) (CIsLeftNeutral)

public theorem CLeftNeutralOnSeparables :
  ∀ x : ℂ, ∀ y : E, CIsLeftNeutral (x ⊗ₜ[ℂ] y) = x • y := by intro x y; simp;

public theorem CRightNeutralOnSeparables :
  ∀ x : E, ∀ y : ℂ, CIsRightNeutral (x ⊗ₜ[ℂ] y) = y • x := by intro x y; simp;
/-
    An element of R is uniquely determined by an isometry from ℂ to R
-/

 @[expose]
public noncomputable def ElementInSpaceAsIso (x : E) (hX : x ≠ 0) : ℂ →ₗᵢ[ℂ] E :=
  LinearIsometry.mk
    (LinearMap.mk
      (AddHom.mk (fun c : ℂ => ((c * ‖x‖⁻¹) : ℂ) • x) (by intro y z; simp; ring; rw[add_smul]))
      (by intro y z; simp; rw[mul_smul, mul_smul, mul_smul]))
    (by intro y; simp; rw[mul_smul, norm_smul, norm_smul,]; simp; calc
      ‖y‖ * (‖x‖⁻¹ * ‖x‖) = ‖y‖ * (‖x‖ * ‖x‖⁻¹) := by rw[mul_comm ‖x‖⁻¹ ‖x‖]
      _ = ‖y‖ * 1 := by rw[Field.mul_inv_cancel ‖x‖]; simp; apply hX
      _ = ‖y‖ := by simp
       )

public theorem ElementInSpacePointsTo (x : E) (hX : x ≠ 0) :
  (ElementInSpaceAsIso x hX).toFun (1 : ℂ) = (‖x‖⁻¹ : ℂ) • x := by unfold ElementInSpaceAsIso; simp


/-
    One can tensor Linear Isometries out
-/

public noncomputable abbrev TensorLinearIsometries (f : E →ₗᵢ[ℂ] G) (g : F →ₗᵢ[ℂ] H) :
  (TensorProduct ℂ E F) →ₗᵢ[ℂ] (TensorProduct ℂ G H) := TensorProduct.mapIsometry f g

/-
    Compute a Tensor of Linear Isometries on Separable states
-/

public theorem TensorLinearIsometriesOnSeparables (f : E →ₗᵢ[ℂ] G) (g : F →ₗᵢ[ℂ] H) :
  ∀ x : E, ∀ y : F, (TensorLinearIsometries f g) (x ⊗ₜ[ℂ] y) = (f x) ⊗ₜ[ℂ] (g y) :=
  by intro x y; rfl


@[simp]
public theorem TensorAssocOverComp {E' F' G' : Type} [H1' : HilbertSpace E'] [H2' : HilbertSpace F']
  [H3' : HilbertSpace G'] (f : E →ₗᵢ[ℂ] E') (g : F →ₗᵢ[ℂ] F') (h : G →ₗᵢ[ℂ] G')
  : LinearIsometry.comp (TensorLinearIsometries f (TensorLinearIsometries g h)) HilbertTensorAssoc.toLinearIsometry =
    LinearIsometry.comp (HilbertTensorAssoc.toLinearIsometry) (TensorLinearIsometries (TensorLinearIsometries f g) h) :=
  by ext x; simp; calc
  (TensorProduct.map f.toLinearMap (TensorProduct.map g.toLinearMap h.toLinearMap)) ((TensorProduct.assoc ℂ E F G) x)
  = ((TensorProduct.map f.toLinearMap (TensorProduct.map g.toLinearMap h.toLinearMap)) ∘ₗ (TensorProduct.assoc ℂ E F G)) x
  := by simp;
  _ = ((TensorProduct.assoc ℂ E' F' G') ∘ₗ ((TensorProduct.map (TensorProduct.map f.toLinearMap g.toLinearMap) h.toLinearMap))) x
  := by rw[TensorProduct.map_map_comp_assoc_eq f.toLinearMap g.toLinearMap h.toLinearMap];

/-
    By linearity, Isometries over tensor spaces are uniquely determined by the image on
    the base spaces
-/

public noncomputable def LinearIsometryFromTensorLeft (f : (TensorProduct ℂ E G) →ₗᵢ[ℂ] F) (y : G) (hY : ‖y‖ = 1) : E →ₗᵢ[ℂ] F :=
  LinearIsometry.mk
  (
    LinearMap.mk
    (
      AddHom.mk (fun x => f (TensorProduct.tmul ℂ x y)) (by intro a b; rw[TensorProduct.add_tmul, LinearIsometry.map_add])
    )
    (by intro m x; simp; rw[<- TensorProduct.smul_tmul']; apply LinearIsometry.map_smul)
  )
  (by intro x; simp; rw[hY]; simp)


public noncomputable def LinearIsometryFromTensorRight (f : (TensorProduct ℂ E G) →ₗᵢ[ℂ] F) (x : E) (hX : ‖x‖ = 1) : G →ₗᵢ[ℂ] F :=
  LinearIsometry.mk
  (
    LinearMap.mk
    (
      AddHom.mk (fun y => f (TensorProduct.tmul ℂ x y)) (by intro a b; rw[TensorProduct.tmul_add, LinearIsometry.map_add])
    )
    (by intro m x; simp)
  )
  (by intro x; simp; rw[hX]; simp)

public noncomputable def LinearIsometryFromTensorProd (E E' F : Type) [HilbertSpace E] [HilbertSpace E']
  [HilbertSpace F] (f : (TensorProduct ℂ E E') →ₗᵢ[ℂ] F) : E × E'→ F :=
  fun c => f (TensorProduct.tmul ℂ c.fst c.snd)


/-
    Expected monoidal properties of the setting
-/

public abbrev IdMap (X : Type) [HilbertSpace X] : X →ₗᵢ[ℂ] X := LinearIsometry.id

@[simp]
public theorem TensorOfIdIsId
  : TensorLinearIsometries (IdMap E) (IdMap F) = IdMap (TensorProduct ℂ E F) :=
    TensorProduct.mapIsometry_id_id

@[simp]
public theorem IdIsNeutralLeft (f : E →ₗᵢ[ℂ] F) : f.comp (IdMap E) = f :=
  by apply LinearIsometry.comp_id

@[simp]
public theorem IdIsNeutralRight (f : E →ₗᵢ[ℂ] F) : (IdMap F).comp f = f :=
  by apply LinearIsometry.comp_id

@[simp]
public theorem TensorFactorises {E' G' : Type}  [HilbertSpace E'] [HilbertSpace G']
  (f : E' →ₗᵢ[ℂ] F) (g : G' →ₗᵢ[ℂ] H) (h : E →ₗᵢ[ℂ] E') (i :G →ₗᵢ[ℂ] G') :
  LinearIsometry.comp (TensorLinearIsometries f g) (TensorLinearIsometries h i) =
  TensorLinearIsometries (LinearIsometry.comp f h) (LinearIsometry.comp g i) :=
  by unfold TensorLinearIsometries; ext x; simp; rw[<- LinearMap.comp_apply, <- TensorProduct.map_comp f.toLinearMap g.toLinearMap h.toLinearMap i.toLinearMap]; rfl

@[simp]
public theorem LinearIsometryEquivalenceComp (f : E ≃ₗᵢ[ℂ] F) (g : F ≃ₗᵢ[ℂ] G) :
    (g.toLinearIsometry ∘ f.toLinearIsometry) = (f.trans g).toLinearIsometry :=
    by rfl

@[simp]
public theorem EquivalenceToIsometryOfSymmLeft (f : E ≃ₗᵢ[ℂ] F) :
  LinearIsometry.comp f.toLinearIsometry f.symm.toLinearIsometry = IdMap F :=
    by ext x; apply LinearIsometryEquiv.apply_symm_apply

@[simp]
public theorem EquivalenceToIsometryOfSymmRight (f : E ≃ₗᵢ[ℂ] F) :
  LinearIsometry.comp  f.symm.toLinearIsometry f.toLinearIsometry  = IdMap E :=
    by ext x; apply LinearIsometryEquiv.symm_apply_apply


/-
    LinearIsometries from ℂ to X are equal iff they agree at (1 : ℂ)
-/


public theorem LinearIsometriesOnCAgree
  (f g : ℂ →ₗᵢ[ℂ] E) : f = g ↔ (f 1) = (g 1) :=
  by apply Iff.intro;intro hyp; rw[hyp]; intro hyp; ext x;
     rw[<- mul_one x]; calc
     f (x * 1) = f (x • 1) := by simp
     _ = x • (f 1) := by rw[LinearIsometry.map_smul]
     _ = x • (g 1) := by rw[hyp]
     _ = g (x • 1) := by rw[<- LinearIsometry.map_smul]
     _ = g (x * 1) := by simp;

public theorem LinearIsometriesOnCAgree'
  (f g : ℂ →ₗᵢ[ℂ] E) : f = g ↔ (f.toFun 1) = (g.toFun 1) :=
  by simp; apply LinearIsometriesOnCAgree

/-
    Computation of the norm in a Hilbert Space
-/

public theorem NormFromInner (z : E) : ‖z‖ = √ (Complex.re (inner ℂ z z))
  := by calc
    ‖z‖ = √(‖z‖ ^ 2)                   := by symm; simp;
     _  = √(Complex.re (inner ℂ z z))  := by rw[EH.norm_sq_eq_re_inner]; rfl

/-
    Normalize vectors
-/

public noncomputable abbrev NormalizeElement (x : E) : E := ‖x‖⁻¹ • x

public theorem ElementIsUnitAndSize (x : E) : ‖x‖ ≠ 0 → x = ‖x‖ • (NormalizeElement x) :=
  by intro h; unfold NormalizeElement; rw[<- mul_smul, Field.mul_inv_cancel ‖x‖]; simp; apply h

public theorem NormOfNormalizedIsOne (x : E) : ‖x‖ ≠ 0 → ‖(NormalizeElement x)‖ = 1 :=
  by intro hX; unfold NormalizeElement; rw[norm_smul]; simp; rw[mul_comm, Field.mul_inv_cancel ‖x‖]; apply hX

public theorem NormZeroIffZero : ∀ x : E, ‖x‖ = 0 ↔ x = 0 :=
  by intro x; apply Iff.trans (normSqZero x) (innerZero x) where
    normSqZero : ∀ x : E, ‖x‖ = 0 ↔ (inner ℂ x x).re = 0 := by intro x; rw[NormFromInner]; simp; apply Real.sqrt_eq_zero; rw[<- Complex.ofReal_pow, Complex.ofReal_re]; apply Even.pow_nonneg; simp
    normSqExpr : ∀ x : E, (inner ℂ x x).re = 0 ↔ (inner ℂ x x) = 0 := by intro x; apply Iff.intro; intro hX; apply Complex.ext; rw[hX]; simp; simp; rw[<- Complex.ofReal_pow, Complex.ofReal_im]; intro h; rw[h]; simp
    innerZero : ∀ x : E, (inner ℂ x x).re = 0 ↔ x = 0 := by intro x; apply Iff.trans (normSqExpr x) (inner_self_eq_zero)

/-
    Induction on separable element
-/


public def StatesAsCombinationOfSeparables (E F : Type) [HilbertSpace E] [HilbertSpace F] :
  TensorProduct ℂ E F ≃
    Submodule.span ℂ {t : TensorProduct ℂ E F | ∃ (m : E) (n : F), m ⊗ₜ[ℂ] n = t} :=
    .mk (fun x => ⟨x, by rw[TensorProduct.span_tmul_eq_top ℂ E F]; simp⟩) (fun a => a.val)
    (by unfold Function.LeftInverse; intro x; simp)
    (by unfold Function.RightInverse; intro x; simp)

public def SepToTensorProp
  (p : (x : TensorProduct ℂ E F) → (x ∈ Submodule.span ℂ {t : TensorProduct ℂ E F | ∃ (m : E) (n : F), m ⊗ₜ[ℂ] n = t}) → Prop)
  : TensorProduct ℂ E F → Prop :=
  fun x => p (StatesAsCombinationOfSeparables E F x) (StatesAsCombinationOfSeparables E F x).prop

public def TensorToSepProp
  (p : TensorProduct ℂ E F → Prop) :
  (x : TensorProduct ℂ E F) → (x ∈ Submodule.span ℂ {t : TensorProduct ℂ E F| ∃ (m : E) (n : F), m ⊗ₜ[ℂ] n = t}) → Prop :=
  fun x hx => p ((StatesAsCombinationOfSeparables E F).symm (Subtype.mk x hx))

public theorem SeparablePropCoherence (p : TensorProduct ℂ E F → Prop) :
   ∀ x, (p x) ↔ ((TensorToSepProp p) (StatesAsCombinationOfSeparables E F x).val (StatesAsCombinationOfSeparables E F x).prop)
  := by intro x; rfl

public theorem TensorInduction
  (property : TensorProduct ℂ E F → Prop)
  (hzero : property 0)
  (hAllBasis : ∀ x1 : E, ∀ x2 : F, property (x1 ⊗ₜ[ℂ] x2))
  (hLinear : ∀ x1 x2 : (TensorProduct ℂ E F), property x1 → property x2 → property (x1 + x2))
  (hmul :  ∀ x : (TensorProduct ℂ E F), ∀ c : ℂ, property x → property (c • x)) :
  ∀ x : (TensorProduct ℂ E F), property x :=
  by intro x; apply
   (
    Submodule.span_induction (p := (TensorToSepProp property))
    (fun x hx => (SeparablePropCoherence property x).mp (by
      have hab : ∃ a b, a ⊗ₜ[ℂ] b = x := hx.out
      rcases hab with ⟨a, b, hfin⟩; rw[<- hfin]; apply hAllBasis a b))
    ((SeparablePropCoherence property 0).mp hzero)
    (fun x y hx hy wx wy => (SeparablePropCoherence property (x + y)).mp (hLinear x y ((SeparablePropCoherence property x).mpr wx) ((SeparablePropCoherence property y).mpr wy)))
    (fun a x hx wx => (SeparablePropCoherence property (a • x)).mp (hmul x a ((SeparablePropCoherence property x).mp wx)))
  ); apply (StatesAsCombinationOfSeparables E F x).prop

/-
    Extensionnality of Linear Isometries on Tensor space
-/

public theorem LinearIsometryExtOnTensor (f g : (TensorProduct ℂ E F) →ₗᵢ[ℂ] G)
  (h :  ∀ x : E, ∀ y : F, f (x ⊗ₜ[ℂ] y) = g (x ⊗ₜ[ℂ] y)) : f = g :=
  LinearIsometry.ext (
      TensorInduction
      (fun x => f x = g x)
      (by rw[LinearIsometry.map_zero, LinearIsometry.map_zero])
      h
      (by intro x y h1 h2; simp; rw[h1, h2])
      (by intro x c h'; simp; rw[h']))

public theorem LinearIsometryExtOnTensorIff (f g : (TensorProduct ℂ E F) →ₗᵢ[ℂ] G) :
  f = g ↔ ∀ x : E, ∀ y : F, f (x ⊗ₜ[ℂ] y) = g (x ⊗ₜ[ℂ] y) :=
  by apply Iff.intro; intro h x y; rw[h]; intro h; apply LinearIsometryExtOnTensor; apply h


/-
    Linear Isometry composition and application -- why is this not in mathlib? did I miss it?
-/

@[simp]
public theorem LinearIsometryCompApply (f : E →ₗᵢ[ℂ] F) (g : F →ₗᵢ[ℂ] G) (x : E) :
  (g.comp f) x = g (f x) := by rfl

/-
    Pi Tensor Product -- TODO, Relies heavily on mathlib, but mathlib has TODOs
-/

-- @[default_instance]
-- public noncomputable instance {I : Type} {H : I → Type} [(i : I) → HilbertSpace (H i)] :
--   NormedAddCommGroup (PiTensorProduct ℂ H) :=
--   AddGroupNorm.toNormedAddCommGroup (_)
--
-- @[default_instance]
-- public noncomputable instance {I : Type} {H : I → Type} [(i : I) → HilbertSpace (H i)] :
--   NormedAddCommGroup (PiTensorProduct ℂ H) :=
--   NormedAddCommGroup.ofAddDist _ _

-- @[default_instance]
-- public noncomputable instance {I : Type} {H : I → Type} [(i : I) → HilbertSpace (H i)] :
--   NormedAddCommGroup (PiTensorProduct ℂ H) :=
--   .ofSeparation (by intro x; rfl)

@[default_instance]
public noncomputable instance HilbertPiTensor {I : Type} {H : I → Type} [(i : I) → HilbertSpace (H i)] :
  HilbertSpace (PiTensorProduct ℂ H) := by sorry

@[expose, implicit_reducible]
public noncomputable def HilbertPiTensorFun (I : Type) (H : I → Type)
  [(i : I) → HilbertSpace (H i)] : HilbertSpace (PiTensorProduct ℂ H) := HilbertPiTensor

end QuantumTypes
