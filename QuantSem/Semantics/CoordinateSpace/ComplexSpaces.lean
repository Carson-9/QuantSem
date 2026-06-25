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
    Tensor products of ℂⁿ-like spaces are isomorphic to ℂᵐ-like spaces
-/

@[default_instance]
instance {n m : ℕ} : Fintype (CatElementQuantumReg ((ComplexSpace n) ⊗ᵣ (ComplexSpace m))).indexing :=
  instFintypeProd (Fin n) (Fin m)


public def ComplexSpaceTensor (n m : ℕ) :
  (CatElementQuantumReg ((ComplexSpace n) ⊗ᵣ (ComplexSpace m))).space
  ≃ₗᵢ[ℂ]
  (CatElementQuantumReg (ComplexSpace (n • m))).space :=
  .mk ( Module.Basis.linearMap
        (CatElementQuantumReg ((ComplexSpace n) ⊗ᵣ (ComplexSpace m))).struct.toBasis
        (CatElementQuantumReg ((ComplexSpace (n • m)))).struct.toBasis)
  (_)



/-
    Coercion of unitary matrices as gates
-/

variable {ι ι1 ι2 : Type}
  [DecidableEq ι] [Fintype ι]
  [DecidableEq ι1] [Fintype ι1]
  [DecidableEq ι2] [Fintype ι2]

public theorem MatrixUnitaryIff (M : Matrix ι ι ℂ) :
  M ∈ Matrix.unitaryGroup ι ℂ ↔ (M ∈ unitary (Matrix ι ι ℂ)) :=
  by apply Iff.intro; intro h; rw[Unitary.mem_iff];
     apply And.intro; rw[Matrix.mem_unitaryGroup_iff'] at h; apply h; rw[Matrix.mem_unitaryGroup_iff] at h; apply h
     intro h; rw[Matrix.mem_unitaryGroup_iff]; rw[Unitary.mem_iff] at h; apply h.right

public def MatrixTensor (N : Matrix.unitaryGroup ι1 ℂ) (M : Matrix.unitaryGroup ι2 ℂ)
  : Matrix.unitaryGroup (ι1 × ι2) ℂ :=
  ⟨Matrix.kronecker N M, Matrix.kronecker_mem_unitary N.mem M.mem⟩


public def MatrixUnitaryStarEquiv :
  Matrix.unitaryGroup ι ℂ  ≃⋆* (unitary (Matrix ι ι ℂ)) :=
  .mk (
  .mk (
    .mk
    (fun x => x) (fun x => x) (by intro x; rfl) (by intro x; rfl))
  (by intro x y; simp))
  (by intro a; simp;)

public noncomputable def MatrixToEuclideanMap :
  Matrix ι ι ℂ ≃ₗ[ℂ] (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
  (Matrix.toEuclideanLin.trans (LinearMap.toContinuousLinearMap))

postfix:max "†" => star

public theorem StarCommutesToLin (M : Matrix ι ι ℂ) :
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

public noncomputable def MatrixEuclideanMapStar :
  Matrix ι ι ℂ ≃⋆* (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
  .mk (.mk (MatrixToEuclideanMap.toEquiv)
    (by intro x y; simp; unfold MatrixToEuclideanMap; simp; rfl))
    (by intro a; simp; apply StarCommutesToLin)


@[default_instance]
public noncomputable instance : Star (EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι) where
  star x := x.symm

public noncomputable def UnitaryMatrixToLinearIsometry :
  (Matrix.unitaryGroup ι ℂ) ≃⋆* (EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι) :=
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

/-
    These coercions commute with composition and Tensor Product
-/


-- Watch out! The algebra inverses matrix multiplication and gate composition notation
public theorem MatrixGateMulComm {n : ℕ} (M N : Matrix.unitaryGroup (Fin n) ℂ) :
  MatrixToGate (M * N) = (MatrixToGate N) ≫ (MatrixToGate M) :=
  by simp; unfold MatrixToGate; simp; rfl


public theorem MatrixGateTensorCom {n m : ℕ} (M : Matrix.unitaryGroup (Fin m) ℂ) (N : Matrix.unitaryGroup (Fin n) ℂ) :
  MatrixToGate (MatrixTensor M N) = (ComplexSpaceTensor n m).toLinearIsometry ≫ ((MatrixToGate M) ⊗ₕ (MatrixToGate N)) ≫ (ComplexSpaceTensor n m).inverse:=
  by simp; sorry


end ComplexSpaces
