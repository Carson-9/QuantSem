/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module


public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis

public import QuantSem.QuantumLib.HilbertSpaces.Basic


open ContinuousLinearMap InnerProductSpace
open scoped InnerProduct ComplexInnerProductSpace
open QuantumTypes

namespace BasisTypes

-- ι should be a set to receive a decidable equality which is better for orthogonality check

public class HilbertSpaceWithBasis (E : Type) (ι : Type) extends  HilbertSpace E, Module.Basis ι ℂ E where
  basisType := ι
  isOrthonormal : Orthonormal ℂ (fun i : ι => toBasis i)


variable {E F G H ι γ κ δ : Type}
  [EH : HilbertSpaceWithBasis E ι] [FH : HilbertSpaceWithBasis F γ]
  [GH : HilbertSpaceWithBasis G κ] [HH : HilbertSpaceWithBasis H δ]

/-
    Hilbert spaces with basis can be composed with the Tensor product
-/


-- The (lack of) excluded middle is both annoying and insightful
@[default_instance]
public noncomputable instance HilbertBasisTensor
  : HilbertSpaceWithBasis (TensorProduct ℂ E F) (ι × γ) where
  repr := (Module.Basis.tensorProduct EH.toBasis FH.toBasis).repr
  isOrthonormal := Orthonormal.basisTensorProduct EH.isOrthonormal FH.isOrthonormal

public noncomputable abbrev HilbertBasisTensorFun (E F ι γ : Type)
  [H1 : HilbertSpaceWithBasis E ι] [H2 : HilbertSpaceWithBasis F γ]
  : HilbertSpaceWithBasis (TensorProduct ℂ E F) (ι × γ) := HilbertBasisTensor

public theorem BasisToHilbertCastCoherence (E F ι γ : Type)
  [H1 : HilbertSpaceWithBasis E ι] [H2 : HilbertSpaceWithBasis F γ] :
  HilbertTensorFun = (HilbertBasisTensorFun E F ι γ).toHilbertSpace := by rfl

/-
    The basis vectors of the tensor space are given by eᵢ ⊗ fⱼ
-/

public theorem BasisOfTensor : ∀ index : ι × γ,
  (HilbertBasisTensorFun E F ι γ).toBasis index =
    TensorProduct.tmul ℂ (EH.toBasis index.fst) (FH.toBasis index.snd) :=
  by intro i; unfold HilbertBasisTensorFun; unfold HilbertBasisTensor; simp
     rw[Module.Basis.tensorProduct_apply' EH.toBasis FH.toBasis i]

/-
    ℂ is the unit of the tensor product. It is a Hilbert space
-/

-- Weird shenanigans in order to avoid having to deal with Finset support proof that
-- becomes invalid when c = 0
@[default_instance]
public noncomputable instance CHilbertBasis : HilbertSpaceWithBasis ℂ (Fin 1) where
  repr := (Module.Basis.ofEquivFun  (LinearEquiv.mk
  (LinearMap.mk (AddHom.mk (fun c => fun _ => c) (by intro x y; ext z; simp))
  (by intro x y; simp; ext z; simp))
  (fun f => f 0)
  ( by unfold Function.LeftInverse; intro x; simp;)
  ( by unfold Function.RightInverse; intro x; simp; ext z; rw[Fin.fin_one_eq_zero z])
  )).repr
  isOrthonormal :=
  by  unfold Orthonormal
      apply And.intro
      intro i; simp; rw[Fin.fin_one_eq_zero i]; simp
      unfold Pairwise; intro i j hneq; rw[Fin.fin_one_eq_zero i] at hneq; rw[Fin.fin_one_eq_zero j] at hneq; contradiction

@[expose, implicit_reducible]
public noncomputable def CIsHilbertBasis : HilbertSpaceWithBasis ℂ (Fin 1) := CHilbertBasis

/-
    By linearity, Isometries over tensor spaces with basis are uniquely determined
    by the image on the original spaces
-/


@[ext]
public theorem LinearIsometryProductBasisExt (f g : (TensorProduct ℂ E F) →ₗᵢ[ℂ] G)
  : (∀ c : E × F, f (TensorProduct.tmul ℂ c.fst c.snd) = g (TensorProduct.tmul ℂ c.fst c.snd)) → (f = g) :=
  by intro h; apply (Module.Basis.ext_linearIsometry (Module.Basis.ofRepr (HilbertBasisTensorFun E F ι γ).repr)); intro i; simp; rw[BasisOfTensor]; apply (h (EH.toBasis i.1, FH.toBasis i.2))

@[ext]
public theorem LinearIsometryBasisExt (f g : E →ₗᵢ[ℂ] F)
  : (∀ i : ι, f (EH.toBasis i) = g (EH.toBasis i)) → (f = g) :=
  by intro h; apply (Module.Basis.ext_linearIsometry EH.toBasis); exact h

/-
    A Linear Isometry can be built from the image of a basis
-/

public noncomputable def LinearIsometryFromBasis (f : ι → F) (hOrth : Orthonormal ℂ f)  : E →ₗᵢ[ℂ] F :=
  LinearMap.isometryOfOrthonormal
    (EH.constr ℂ f)
    (EH.isOrthonormal)
    (by unfold Orthonormal; apply And.intro; intro i; unfold Orthonormal at hOrth; simp;
        apply hOrth.left i; intro i j h; simp; apply hOrth.right; apply h)


/-
    Pi notation for a family of Hilbert Spaces (Need to be a module at least)
-/


@[default_instance]
public noncomputable instance PiHilbertBasisTensor {I : Type} [Finite I] {H : I → Type}
  {ι : I → Type} [S : (i : I) → HilbertSpaceWithBasis (H i) (ι i)]
  : HilbertSpaceWithBasis (PiTensorProduct ℂ (fun i : I => H i)) (Π i : I, ι i) := by sorry
  -- repr := (Basis.piTensorProduct (fun i : I => (S i).toBasis)).repr
  -- isOrthonormal := _

public noncomputable abbrev PiHilbertBasisTensorFun (I : Type) [Finite I]
  (H ι : I → Type) [S : (i : I) → HilbertSpaceWithBasis (H i) (ι i)]
  : HilbertSpaceWithBasis (PiTensorProduct ℂ H) (Π i : I, ι i) := PiHilbertBasisTensor



end BasisTypes
