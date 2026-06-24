/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/

module


public import QuantSem.Syntax.Category.Category
public import QuantSem.Syntax.WithBasis.WithBasis
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Algebra.Star.LinearMap

namespace ComplexSpaces

open BasisTypes
open BasisRegister
open BasisState
open BasisGate

open CategoryTheory
open LinearMap


/-
    The classical setting for quantum computation is the Euclidean Spaces ℂⁿ
-/

public noncomputable instance EuclideanHilbertBasis (n : ℕ) :
  HilbertSpaceWithBasis (EuclideanSpace ℂ (Fin n)) (Fin n) where
  repr := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.repr
  isOrthonormal := OrthonormalBasis.orthonormal (EuclideanSpace.basisFun (Fin n) ℂ)

public noncomputable abbrev ComplexSpace (n : ℕ) : TypeBasisRegister :=
  ⟨EuclideanSpace ℂ (Fin n), ⟨Fin n, (EuclideanHilbertBasis n)⟩⟩

public noncomputable abbrev QubitSpace : TypeBasisRegister := ComplexSpace 2
public noncomputable abbrev QutritSpace : TypeBasisRegister := ComplexSpace 3


/-
    Coercion of unitary matrices as gates
-/


public theorem MatrixUnitaryIff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
  M ∈ Matrix.unitaryGroup (Fin n) ℂ ↔ (M ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) :=
  by apply Iff.intro; intro h; rw[Unitary.mem_iff];
     apply And.intro; rw[Matrix.mem_unitaryGroup_iff'] at h; apply h; rw[Matrix.mem_unitaryGroup_iff] at h; apply h
     intro h; rw[Matrix.mem_unitaryGroup_iff]; rw[Unitary.mem_iff] at h; apply h.right


public def MatrixUnitaryStarEquiv {n : ℕ} :
  Matrix.unitaryGroup (Fin n) ℂ  ≃⋆* (unitary (Matrix (Fin n) (Fin n) ℂ)) :=
  .mk (
  .mk (
    .mk
    (fun x => x) (fun x => x) (by intro x; rfl) (by intro x; rfl))
  (by intro x y; simp))
  (by intro a; simp;)

public noncomputable def MatrixToEuclideanMap {n : ℕ} :
  Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  (Matrix.toEuclideanLin.trans (LinearMap.toContinuousLinearMap))

postfix:max "†" => star

public theorem StarCommutesToLin {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
  MatrixToEuclideanMap M† = (MatrixToEuclideanMap M)†
  := by unfold MatrixToEuclideanMap; simp;
        unfold ContinuousLinearMap.instStarId; simp;
        unfold Matrix.instStar; simp;
        rw[Matrix.toEuclideanLin_conjTranspose_eq_adjoint];
        rfl

-- Useful lemmas but deprecated :(
-- Matrix.toEuclideanLin_toLp
-- Matrix.piLp_ofLp_toEuclideanLin
-- Matrix.toEuclideanLin_apply
-- Matrix.ofLp_toEuclideanLin_apply

public noncomputable def MatrixEuclideanMapStar {n : ℕ} :
  Matrix (Fin n) (Fin n) ℂ ≃⋆* (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  .mk (.mk (MatrixToEuclideanMap.toEquiv)
    (by intro x y; simp; unfold MatrixToEuclideanMap; simp; rfl))
    (by intro a; simp; apply StarCommutesToLin)


@[default_instance]
public noncomputable instance {n : ℕ} : Star (EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) where
  star x := x.symm

public noncomputable def UnitaryMatrixToLinearIsometry {n : ℕ} :
  (Matrix.unitaryGroup (Fin n) ℂ) ≃⋆* (EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :=
  (MatrixUnitaryStarEquiv.trans (Unitary.mapEquiv MatrixEuclideanMapStar)).trans
  (.mk Unitary.linearIsometryEquiv
  (by intro a; unfold Unitary.linearIsometryEquiv; simp; rfl))


/-
    Coercion of Matrices to Gates
-/

@[coe]
public noncomputable def MatrixToGate {n : ℕ} (M : Matrix.unitaryGroup (Fin n) ℂ) : BasisGateType (ComplexSpace n) (ComplexSpace n)
  := (UnitaryMatrixToLinearIsometry M).toLinearIsometry

public noncomputable instance {n : ℕ} : Coe (Matrix.unitaryGroup (Fin n) ℂ) (BasisGateType (ComplexSpace n) (ComplexSpace n)) where
  coe := MatrixToGate

@[coe]
public noncomputable def MatrixToGate' {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
  (h : ∀ x : (EuclideanSpace ℂ (Fin n)),
  ‖(Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (EuclideanSpace.basisFun (Fin n) ℂ).toBasis M) x‖ = ‖x‖) :
  BasisGateType (ComplexSpace n) (ComplexSpace n) :=
  LinearIsometry.mk
    (Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (EuclideanSpace.basisFun (Fin n) ℂ).toBasis M)
    (by apply h)

/-
    These coercions commute with composition and Tensor Product
-/

public theorem MatrixGateMulComm {n : ℕ} (M N : Matrix.unitaryGroup (Fin n) ℂ) :
  MatrixToGate (M * N) = (MatrixToGate M) ≫ (MatrixToGate N) :=
  by simp; unfold MatrixToGate; simp;
     rw[UnitaryMatrixToLinearIsometry.map_mul']

  --rw[LinearIsometry.mul_def (UnitaryMatrixToLinearIsometry M) (UnitaryMatrixToLinearIsometry N)]

public theorem MatrixGateTensorCom {n : ℕ} (M N : Matrix.unitaryGroup (Fin n) ℂ) :
  MatrixToGate (Matrix.kronecker M  N) = (MatrixToGate M) ⊗ₕ (MatrixToGate N) :=
  by simp; sorry


end ComplexSpaces
