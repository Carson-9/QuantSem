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


@[expose, implicit_reducible]
public noncomputable def HilbertTensorFun (E F : Type) [H1 : HilbertSpace E] [H2 : HilbertSpace F]
  : HilbertSpace (TensorProduct ℂ E F) := HilbertTensor

public noncomputable def HilbertTensorAssoc (E F G : Type) [H1 : HilbertSpace E] [H2 : HilbertSpace F]
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
    One can tensor Linear Isometries out
-/

@[expose]
public noncomputable def TensorLinearIsometries {E F G H : Type} [HilbertSpace E] [HilbertSpace F] [HilbertSpace G]
  [HilbertSpace H] (f : E →ₗᵢ[ℂ] G) (g : F →ₗᵢ[ℂ] H) :
  (TensorProduct ℂ E F) →ₗᵢ[ℂ] (TensorProduct ℂ G H) := TensorProduct.mapIsometry f g

/-
    Expected monoidal properties of the setting
-/

public abbrev IdMap (E : Type) [HilbertSpace E] : E →ₗᵢ[ℂ] E := LinearIsometry.id

public theorem TensorOfIdIsId (E F : Type) [E' : HilbertSpace E] [F' : HilbertSpace F]
  : @TensorLinearIsometries E F E F E' F' E' F' (IdMap E) (IdMap F) =
    IdMap (TensorProduct ℂ E F)
  := TensorProduct.mapIsometry_id_id

public theorem IdIsNeutralLeft (E F : Type) [HilbertSpace E] [HilbertSpace F] (f : E →ₗᵢ[ℂ] F):
  f.comp (IdMap E) = f := by apply LinearIsometry.comp_id

public theorem IdIsNeutralRight (E F : Type) [HilbertSpace E] [HilbertSpace F] (f : E →ₗᵢ[ℂ] F):
  (IdMap F).comp f = f := by apply LinearIsometry.comp_id

public theorem TensorFactorises (E E' F G G' H : Type) [HilbertSpace E] [HilbertSpace E']
  [HilbertSpace F] [HilbertSpace G] [HilbertSpace G'] [HilbertSpace H]
  (f : E' →ₗᵢ[ℂ] F) (g : G' →ₗᵢ[ℂ] H) (h : E →ₗᵢ[ℂ] E') (i :G →ₗᵢ[ℂ] G') :
  LinearIsometry.comp (TensorLinearIsometries f g) (TensorLinearIsometries h i) =
  TensorLinearIsometries (LinearIsometry.comp f h) (LinearIsometry.comp g i) :=
  by unfold TensorLinearIsometries; sorry


end QuantumTypes
