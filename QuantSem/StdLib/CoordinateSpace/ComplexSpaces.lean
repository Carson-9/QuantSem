/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/

module


public import QuantSem.Imports.AbstractBasis
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Algebra.Star.LinearMap

namespace ComplexSpaces

open BasisTypes
open AbstractBasisRegister
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

public noncomputable abbrev ComplexSpace (n : ℕ) : BasisRegister :=
  .mk (EuclideanSpace ℂ (Fin n)) (Fin n) (EuclideanHilbertBasis n)

public noncomputable abbrev QubitSpace : BasisRegister := ComplexSpace 2
public noncomputable abbrev QutritSpace : BasisRegister := ComplexSpace 3

@[simp]
public theorem ComplexSpaceNormIsEuclideanNorm {n : ℕ} (x : (ComplexSpace n).space) :
  (ComplexSpace n).struct.toNorm.norm x = ‖x‖ := by rfl

public noncomputable abbrev ComplexSpaceDefaultState (n : ℕ) {hn : n > 0} : (ComplexSpace n).space :=
  (ComplexSpace n).struct.toBasis ((@Fin.mk n 0 (by apply hn)))

/-
    Tensor products of ℂⁿ-like spaces are isomorphic to ℂᵐ-like spaces
-/


public def FinTypeFolding {n m : ℕ} : Fin n × Fin m ≃ Fin (n • m) :=
  .mk
  (fun (x, y) => Fin.mkDivMod x y)
  (fun x => (Fin.divNat x, Fin.modNat x))
  (by unfold Function.LeftInverse; simp)
  (by unfold Function.RightInverse Function.LeftInverse; simp)

public theorem FinTypeFoldingDifferent {n m : ℕ} (i j : Fin n × Fin m) :
  i ≠ j ↔ FinTypeFolding i ≠ FinTypeFolding j :=
  by apply Iff.intro; intro h; simp; apply h; intro h; simp at h; apply h

public theorem FinTypeFoldingDifferent' {n m : ℕ} (i j : (BasisRegisterTensor (ComplexSpace n) (ComplexSpace m)).indexing) :
  i ≠ j ↔ FinTypeFolding i ≠ FinTypeFolding j :=
  by apply FinTypeFoldingDifferent

@[default_instance]
public instance {n m : ℕ} : Fintype (BasisRegisterTensor (ComplexSpace n) (ComplexSpace m)).indexing :=
  instFintypeProd (Fin n) (Fin m)

@[default_instance]
public instance {n m : ℕ} : DecidableEq (BasisRegisterTensor (ComplexSpace n) (ComplexSpace m)).indexing :=
  instDecidableEqProd

public noncomputable def ComplexSpaceTensor (n m : ℕ) :
  (BasisRegisterTensor (ComplexSpace n) (ComplexSpace m)).space ≃ₗᵢ[ℂ] (ComplexSpace (n • m)).space :=
  LinearEquiv.isometryOfOrthonormal

    (Module.Basis.equiv
        (BasisRegisterTensor (ComplexSpace n) (ComplexSpace m)).struct.toBasis
        ((ComplexSpace (n • m)).struct.toBasis)
        (FinTypeFolding))

    (BasisRegisterTensor (ComplexSpace n) (ComplexSpace m)).struct.isOrthonormal

    (by apply And.intro; intro i; simp; apply (ComplexSpace (n • m)).struct.isOrthonormal.left;
        simp; intro i j h; rw[FinTypeFoldingDifferent' i j] at h; apply (ComplexSpace (n • m)).struct.isOrthonormal.right; apply h)

-- public theorem SpaceTensorBasisState {n m : ℕ} (i : Fin (n • m)) :
--   (@GetBasisState (ComplexSpace (n • m)) i) ≫ (ComplexSpaceTensor n m).symm.toLinearIsometry =
--     (@GetBasisState (ComplexSpace n) (Fin.divNat i)) ⊗ₛ (@GetBasisState (ComplexSpace m) (Fin.modNat i)) :=
--     by sorry

/-
    For Pi notation
-/

-- public def PiFinTypeFolding {n : ℕ} (f : Fin n → ℕ) : Π i : Fin n, Fin (f i) ≃ Fin (∏ i : Fin n, f i) :=
--   .mk
--   (fun pi => Fin.mkDivMod x y)
--   (fun x => (Fin.divNat x, Fin.modNat x))
--   (by unfold Function.LeftInverse; simp)
--   (by unfold Function.RightInverse Function.LeftInverse; simp)



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

@[simp]
public theorem ReindexAlgEquivStar {m n : Type*} [Fintype n] [Fintype m]  [DecidableEq m] [DecidableEq n]
  (e : m ≃ n) (M : Matrix m m ℂ) :
  star (Matrix.reindexAlgEquiv ℂ ℂ e M) = (Matrix.reindexAlgEquiv ℂ ℂ e (star M)) :=
  by simp; unfold star Matrix.instStar; simp;

public def MatrixTensor' {n m : ℕ} (N : Matrix.unitaryGroup (Fin n) ℂ) (M : Matrix.unitaryGroup (Fin m) ℂ)
  : Matrix.unitaryGroup (Fin (n • m)) ℂ :=
  ⟨ Matrix.reindexAlgEquiv ℂ ℂ FinTypeFolding (MatrixTensor N M),
  by rw[Matrix.mem_unitaryGroup_iff]; rw[ReindexAlgEquivStar]; rw[<- map_mul]; rw[tensorunit]; simp⟩
  where tensorunit : (MatrixTensor N M).val * star (MatrixTensor N M).val = 1 := by rw[<- Matrix.mem_unitaryGroup_iff]; apply (MatrixTensor N M).prop

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

public instance FinDimEuclidean {n : ℕ} : FiniteDimensional ℂ (ComplexSpace n).space :=
  Module.Basis.finiteDimensional_of_finite (ComplexSpace n).struct.toBasis

@[coe]
public noncomputable def GateToMatrix {n : ℕ} (G : BasisGateType (ComplexSpace n) (ComplexSpace n)) : Matrix.unitaryGroup (Fin n) ℂ
  := (UnitaryMatrixToLinearIsometry.symm (G.toLinearIsometryEquiv (by rfl)))

public noncomputable instance {n : ℕ} : Coe (BasisGateType (ComplexSpace n) (ComplexSpace n)) (Matrix.unitaryGroup (Fin n) ℂ) where
  coe := GateToMatrix




/-
    Coercions of Unit vectors to States
-/

public abbrev nDimUnitVector (n : ℕ) := {v : (EuclideanSpace ℂ (Fin n)) // ‖v‖ = 1}

@[coe]
public noncomputable def UnitVectorToState {n : ℕ} (v : nDimUnitVector n) : BasisStateSpace (ComplexSpace n) :=
  (SyntacticState.QuantumStateSelection v.val v.prop)


@[coe]
public noncomputable def StateToUnitVector {n : ℕ} (s : BasisStateSpace (ComplexSpace n)) : nDimUnitVector n :=
  .mk (s.toFun ((1 : ℂ) / (‖(1 : ℂ)‖ : ℂ))) (by simp; sorry)

public noncomputable instance {n : ℕ} : Coe (nDimUnitVector n) (BasisStateSpace (ComplexSpace n)) where
  coe := UnitVectorToState

public noncomputable instance {n : ℕ} : Coe (BasisStateSpace (ComplexSpace n)) (nDimUnitVector n) where
  coe := StateToUnitVector


-- Need to fix the categories first
--public noncomputable def UnitVectorToState' {n : ℕ} :
--  (nDimUnitVector n) ≃ BasisStateSpace (ComplexSpace n) :=
--  .mk
--  (fun v => @BasisStateSelection (ComplexSpace n) v.val v.prop)
--  (fun s => Subtype.mk (s.toFun (1 : ℂ)) (by simp; rw[s.norm_map (1 : ℂ)]))
--  (by unfold Function.LeftInverse; intro x; simp; rw[Subtype.ext_iff]; rfl)
--  (by unfold Function.RightInverse Function.LeftInverse; simp; intro x; simp)


/-
    These coercions commute with composition and Tensor Product
-/


-- Watch out! The algebra inverses matrix multiplication and gate composition notation
@[simp]
public theorem MatrixGateMulComm {n : ℕ} (M N : Matrix.unitaryGroup (Fin n) ℂ) :
  (MatrixToGate N) ≫ (MatrixToGate M) = MatrixToGate (M * N) :=
  by simp; unfold MatrixToGate; simp; rfl

@[simp]
public theorem MatrixStateEvolve {n : ℕ} (M : Matrix.unitaryGroup (Fin n) ℂ)
  (v : (nDimUnitVector n)) :
  (UnitVectorToState v) ≫ (MatrixToGate M) =
    UnitVectorToState (Subtype.mk
      ((UnitaryMatrixToLinearIsometry M).toLinearIsometry v.val)
      (by simp; apply v.prop)) := by simp; sorry

public theorem MatrixGateTensorCom {n m : ℕ} (M : Matrix.unitaryGroup (Fin m) ℂ) (N : Matrix.unitaryGroup (Fin n) ℂ) :
  MatrixToGate (MatrixTensor' M N) = (ComplexSpaceTensor m n).symm.toLinearIsometry ≫
    ((MatrixToGate M) ⊗ₕ (MatrixToGate N)) ≫ (ComplexSpaceTensor m n).toLinearIsometry :=
  by simp; apply GateExtBasis; intro i;
      unfold MatrixTensor'; simp; sorry

 --Unitary.tmul_mem

/-
    Fin dim matrix product expression
-/

public theorem FinDimMatrixMul {n m p : ℕ} (M : Matrix (Fin n) (Fin m) ℂ) (N : Matrix (Fin m) (Fin p) ℂ)
  : ∀ i : (Fin n), ∀ j : (Fin p), (M * N) i j = ∑ k : (Fin m), (M i k) * (N k j) :=
  by intro i j; rfl

/-
    Matrix i-th column is the image of the i-th basis vector
-/



end ComplexSpaces
