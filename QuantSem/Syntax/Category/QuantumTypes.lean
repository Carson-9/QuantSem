/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module


public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.CategoryTheory.Category.Basic

open ContinuousLinearMap InnerProductSpace
open scoped InnerProduct ComplexInnerProductSpace
open CategoryTheory

namespace QuantumTypes

public class HilbertSpace (E : Type) extends NormedAddCommGroup E, InnerProductSpace ℂ E, CompleteSpace E
  -- An inner product space defines a norm (more than the seminorm promised)
  -- norm_derived_from_inner : norm = InnerProductSpace.toNormedSpace.norm

public class QuantumType (E : Type) extends HilbertSpace E where
  vecAdd : E → E → E := HilbertSpace.toNormedAddCommGroup.add
  innerProd : E → E → ℂ := HilbertSpace.toInnerProductSpace.inner
  normFun : E → ℝ := HilbertSpace.toNormedAddCommGroup.norm

@[expose]
public def TypeQuantumTypes : Type 1 := Σ E, QuantumType E

@[default_instance]
instance (E : TypeQuantumTypes) : SeminormedAddCommGroup E.fst :=
  E.snd.toSeminormedAddCommGroup

@[default_instance]
instance : Category TypeQuantumTypes where
  Hom T1 T2 :=  T1.fst →ₗᵢ[ℂ] T2.fst
  id T1 := LinearIsometry.id
  comp f1 f2 := LinearIsometry.comp f2 f1




/-
    Hilbert spaces can be composed with the Tensor product
-/


@[default_instance]
public noncomputable instance HilbertTensor {E F : Type} [H1 : HilbertSpace E] [H2 : HilbertSpace F]
  : HilbertSpace (TensorProduct ℂ E F) where
  norm := TensorProduct.instNormedAddCommGroup.norm
  smul_zero := TensorProduct.instInnerProductSpace.smul_zero
  smul_add := TensorProduct.instInnerProductSpace.smul_add
  add_smul := TensorProduct.instInnerProductSpace.add_smul
  zero_smul := TensorProduct.instInnerProductSpace.zero_smul
  norm_smul_le := TensorProduct.instInnerProductSpace.norm_smul_le
  norm_sq_eq_re_inner := TensorProduct.instInnerProductSpace.norm_sq_eq_re_inner
  conj_inner_symm := TensorProduct.instInnerProductSpace.conj_inner_symm
  add_left := TensorProduct.instInnerProductSpace.add_left
  smul_left := TensorProduct.instInnerProductSpace.smul_left
  complete := by intro f cauchy_f; sorry


public noncomputable abbrev HilbertTensorFun (E F : Type) [H1 : HilbertSpace E] [H2 : HilbertSpace F]
  : HilbertSpace (TensorProduct ℂ E F) := HilbertTensor

public noncomputable abbrev HilbertTensorAssoc (E F G : Type) [H1 : HilbertSpace E] [H2 : HilbertSpace F]
  [H3 : HilbertSpace G] :
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

@[expose]
public noncomputable def CIsLeftNeutral (E : Type) [HilbertSpace E] :
  TensorProduct ℂ ℂ E ≃ₗᵢ[ℂ] E :=
  TensorProduct.lidIsometry ℂ E

@[expose]
public noncomputable def CIsRightNeutral (E : Type) [HilbertSpace E] :
  TensorProduct ℂ E ℂ ≃ₗᵢ[ℂ] E :=
  LinearIsometryEquiv.trans (TensorProduct.commIsometry ℂ E ℂ) (CIsLeftNeutral E)


/-
    An element of R is uniquely determined by an isometry from ℂ to R
-/

 @[expose]
public noncomputable def ElementInSpaceAsIso (E : Type) [E' : HilbertSpace E] (x : E) (hX : x ≠ 0)
  : ℂ →ₗᵢ[ℂ] E :=
  LinearIsometry.mk
    (LinearMap.mk
      (AddHom.mk (fun c : ℂ => ((c * ‖x‖⁻¹) : ℂ) • x) (by intro y z; simp; ring; rw[E'.add_smul]))
      (by intro y z; simp; rw[E'.mul_smul, E'.mul_smul, E'.mul_smul]))
    (by intro y; simp; rw[E'.mul_smul, norm_smul, norm_smul,]; simp; calc
      ‖y‖ * (‖x‖⁻¹ * ‖x‖) = ‖y‖ * (‖x‖ * ‖x‖⁻¹) := by rw[mul_comm ‖x‖⁻¹ ‖x‖]
      _ = ‖y‖ * 1 := by rw[Field.mul_inv_cancel ‖x‖]; simp; apply hX
      _ = ‖y‖ := by simp
       )

public theorem ElementInSpacePointsTo (E : Type)  [E' : HilbertSpace E] (x : E) (hX : x ≠ 0) :
  (ElementInSpaceAsIso E x hX).toFun (1 : ℂ) = (‖x‖⁻¹ : ℂ) • x := by unfold ElementInSpaceAsIso; simp


/-
    One can tensor Linear Isometries out
-/

public noncomputable abbrev TensorLinearIsometries {E F G H : Type} [HilbertSpace E] [HilbertSpace F] [HilbertSpace G]
  [HilbertSpace H] (f : E →ₗᵢ[ℂ] G) (g : F →ₗᵢ[ℂ] H) :
  (TensorProduct ℂ E F) →ₗᵢ[ℂ] (TensorProduct ℂ G H) := TensorProduct.mapIsometry f g



@[simp]
public theorem TensorAssocOverComp (E E' F F' G G' : Type) [H1 : HilbertSpace E]
  [H1' : HilbertSpace E'] [H2 : HilbertSpace F] [H2' : HilbertSpace F'] [H3 : HilbertSpace G]
  [H3' : HilbertSpace G'] (f : E →ₗᵢ[ℂ] E') (g : F →ₗᵢ[ℂ] F') (h : G →ₗᵢ[ℂ] G')
  : LinearIsometry.comp (TensorLinearIsometries f (TensorLinearIsometries g h)) (HilbertTensorAssoc E F G).toLinearIsometry =
    LinearIsometry.comp ((HilbertTensorAssoc E' F' G').toLinearIsometry) (TensorLinearIsometries (TensorLinearIsometries f g) h) :=
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

public noncomputable def LinearIsometryFromTensorLeft (E E' F : Type) [HilbertSpace E] [HilbertSpace E']
  [HilbertSpace F] (f : (TensorProduct ℂ E E') →ₗᵢ[ℂ] F) (y : E') (hY : ‖y‖ = 1) : E →ₗᵢ[ℂ] F :=
  LinearIsometry.mk
  (
    LinearMap.mk
    (
      AddHom.mk (fun x => f (TensorProduct.tmul ℂ x y)) (by intro a b; rw[TensorProduct.add_tmul, LinearIsometry.map_add])
    )
    (by intro m x; simp; rw[<- TensorProduct.smul_tmul']; apply LinearIsometry.map_smul)
  )
  (by intro x; simp; rw[hY]; simp)


public noncomputable def LinearIsometryFromTensorRight (E E' F : Type) [HilbertSpace E] [HilbertSpace E']
  [HilbertSpace F] (f : (TensorProduct ℂ E E') →ₗᵢ[ℂ] F) (x : E) (hX : ‖x‖ = 1) : E' →ₗᵢ[ℂ] F :=
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

public abbrev IdMap (E : Type) [HilbertSpace E] : E →ₗᵢ[ℂ] E := LinearIsometry.id

@[simp]
public theorem TensorOfIdIsId (E F : Type) [E' : HilbertSpace E] [F' : HilbertSpace F]
  : @TensorLinearIsometries E F E F E' F' E' F' (IdMap E) (IdMap F) =
    IdMap (TensorProduct ℂ E F)
  := TensorProduct.mapIsometry_id_id

@[simp]
public theorem IdIsNeutralLeft (E F : Type) [HilbertSpace E] [HilbertSpace F] (f : E →ₗᵢ[ℂ] F):
  f.comp (IdMap E) = f := by apply LinearIsometry.comp_id

@[simp]
public theorem IdIsNeutralRight (E F : Type) [HilbertSpace E] [HilbertSpace F] (f : E →ₗᵢ[ℂ] F):
  (IdMap F).comp f = f := by apply LinearIsometry.comp_id

@[simp]
public theorem TensorFactorises (E E' F G G' H : Type) [HilbertSpace E] [HilbertSpace E']
  [HilbertSpace F] [HilbertSpace G] [HilbertSpace G'] [HilbertSpace H]
  (f : E' →ₗᵢ[ℂ] F) (g : G' →ₗᵢ[ℂ] H) (h : E →ₗᵢ[ℂ] E') (i :G →ₗᵢ[ℂ] G') :
  LinearIsometry.comp (TensorLinearIsometries f g) (TensorLinearIsometries h i) =
  TensorLinearIsometries (LinearIsometry.comp f h) (LinearIsometry.comp g i) :=
  by unfold TensorLinearIsometries; ext x; simp; rw[<- LinearMap.comp_apply, <- TensorProduct.map_comp f.toLinearMap g.toLinearMap h.toLinearMap i.toLinearMap]; rfl

@[simp]
public theorem LinearIsometryEquivalenceComp {E E' E'' : Type} [HilbertSpace E]
  [HilbertSpace E'] [HilbertSpace E''] (f : E ≃ₗᵢ[ℂ] E') (g : E' ≃ₗᵢ[ℂ] E'') :
    (g.toLinearIsometry ∘ f.toLinearIsometry) = (f.trans g).toLinearIsometry :=
    by rfl

@[simp]
public theorem EquivalenceToIsometryOfSymmLeft {E E' : Type} [HilbertSpace E] [HilbertSpace E']
  (f : E ≃ₗᵢ[ℂ] E') :  LinearIsometry.comp f.toLinearIsometry f.symm.toLinearIsometry = IdMap E' :=
    by unfold LinearIsometry.comp; ext; simp;


@[simp]
public theorem EquivalenceToIsometryOfSymmRight {E E' : Type} [HilbertSpace E] [HilbertSpace E']
  (f : E ≃ₗᵢ[ℂ] E') : LinearIsometry.comp  f.symm.toLinearIsometry f.toLinearIsometry  = IdMap E :=
    by unfold LinearIsometry.comp; ext; simp;


/-
    LinearIsometries from ℂ to X are equal iff they agree at (1 : ℂ)
-/


public theorem LinearIsometriesOnCAgree {E : Type} [HilbertSpace E]
  (f g : ℂ →ₗᵢ[ℂ] E) : f = g ↔ (f 1) = (g 1) :=
  by apply Iff.intro;intro hyp; rw[hyp]; intro hyp; ext x;
     rw[<- mul_one x]; calc
     f (x * 1) = f (x • 1) := by simp
     _ = x • (f 1) := by rw[LinearIsometry.map_smul]
     _ = x • (g 1) := by rw[hyp]
     _ = g (x • 1) := by rw[<- LinearIsometry.map_smul]
     _ = g (x * 1) := by simp;
/-
    Computation of the norm in a Hilbert Space
-/

public theorem NormFromInner (E : Type) [E' : HilbertSpace E] (z : E) :
  ‖z‖ = √ (Complex.re (E'.inner z z)) :=
  by calc
    ‖z‖ = √(‖z‖ ^ 2)                    := by symm; simp;
     _  = √(Complex.re (E'.inner z z))  := by rw[E'.norm_sq_eq_re_inner]; rfl



end QuantumTypes
