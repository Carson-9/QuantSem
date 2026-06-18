/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module


public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.Analysis.InnerProductSpace.l2Space

public import QuantSem.Syntax.Category.QuantumTypes


open ContinuousLinearMap InnerProductSpace
open scoped InnerProduct ComplexInnerProductSpace
open CategoryTheory
open QuantumTypes

namespace BasisTypes

public class HilbertSpaceWithBasis (E : Type) (ι : Type) extends HilbertSpace E where
  basisType := ι
  basis : HilbertBasis ι ℂ E


/-
    Hilbert spaces with basis can be composed with the Tensor product
-/


public def IsometricTensorEquivLPSequence (ι κ : Type)
  : TensorProduct ℂ (lp (fun (x : ι) => ℂ) 2) (lp (fun (x : κ) => ℂ) 2) ≃ₗᵢ[ℂ] (lp (fun x : (ι × κ) => ℂ) 2) :=
  LinearIsometryEquiv.mk
  ( LinearEquiv.symm (LinearEquiv.mk
    ( LinearMap.mk (AddHom.mk (fun x => _) ( _ )) (_) )
    ( _ )
    ( _ )
    ( _ ))
  )
  ( _ )

@[default_instance]
public noncomputable instance HilbertBasisTensor {E F : Type} {ι γ : Type}
  [H1 : HilbertSpaceWithBasis E ι] [H2 : HilbertSpaceWithBasis F γ]
  : HilbertSpaceWithBasis (TensorProduct ℂ E F) (ι × γ) where
  basis := .ofRepr (LinearIsometryEquiv.mk
  ((TensorProduct.congr (H1.basis) (H2.basis)) ≪≫ₗ (finsuppTensorFinsuppLid ℂ ℂ ι γ))
  _

  )
    --(TensorProduct.congr (H1.basis) (H2.basis)) ≪≫ₗ (finsuppTensorFinsuppLid ℂ ℂ ι γ)


public noncomputable abbrev HilbertBasisTensorFun (E F : Type) (ι γ : Type)
  [H1 : HilbertSpaceWithBasis E ι] [H2 : HilbertSpaceWithBasis F γ]
  : HilbertSpaceWithBasis (TensorProduct ℂ E F) (ι × γ) := HilbertBasisTensor


public theorem BasisToHilbertCastCoherence (E F : Type) (ι γ : Type) [H1 : HilbertSpaceWithBasis E ι]
  [H2 : HilbertSpaceWithBasis F γ] :
  HilbertTensorFun E F =
  (HilbertBasisTensorFun E F ι γ).toHilbertSpace := by rfl

/-
    The basis vectors of the tensor space are given by eᵢ ⊗ fⱼ
-/

public theorem BasisOfTensor (E F : Type) (ι γ : Type) [H1 : HilbertSpaceWithBasis E ι]
  [H2 : HilbertSpaceWithBasis F γ] :
  ∀ index : ι × γ, (HilbertBasisTensorFun E F ι γ).toBasis index =
    TensorProduct.tmul ℂ (H1.toBasis index.fst) (H2.toBasis index.snd) :=
  by intro i; sorry -- rw[<- finsuppTensorFinsupp_apply ℂ ℂ E F ι γ H1.toBasis H2.toBasis i.1 i.2];


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

@[expose, implicit_reducible]
public noncomputable def CIsHilbertBasis : HilbertSpaceWithBasis ℂ (Fin 1) := CHilbertBasis

/-
    By linearity, Isometries over tensor spaces with basis are uniquely determined
    by the image on the original spaces
-/


@[ext]
public theorem LinearIsometryBasisExt (E E' F ι κ γ : Type) [EH : HilbertSpaceWithBasis E ι]
  [E'H : HilbertSpaceWithBasis E' κ] [F' : HilbertSpaceWithBasis F γ] (f g : (TensorProduct ℂ E E') →ₗᵢ[ℂ] F)
  : (∀ c : E × E', f (TensorProduct.tmul ℂ c.fst c.snd) = g (TensorProduct.tmul ℂ c.fst c.snd)) → (f = g) :=
  by intro h; apply (Module.Basis.ext_linearIsometry (Module.Basis.ofRepr (HilbertBasisTensorFun E E' ι κ).repr)); intro i; simp; rw[BasisOfTensor]; apply (h (EH.toBasis i.1, E'H.toBasis i.2))

end BasisTypes
