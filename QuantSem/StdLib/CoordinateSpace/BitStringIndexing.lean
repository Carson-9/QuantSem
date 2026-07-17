/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/

module

public import QuantSem.StdLib.CoordinateSpace.ComplexSpaces
public import Batteries.Data.BitVec.Basic
public import Batteries.Data.Vector.Lemmas

open AbstractBasisRegister
open BasisState
open ComplexSpaces

namespace BitStringIndexing

public instance : Coe Bool (Fin 2) where
  coe := fun b => if b then 1 else 0

public instance : Coe QubitSpace.indexing Bool where
  coe := fun i => i == 1

public def QubitIndexingAsBool : QubitSpace.indexing ≃ Bool :=
  .mk (fun i => i == 1) (fun b => b) (by intro x; simp; fin_cases x; rfl; rfl) (by intro x; simp; fin_cases x; rfl; rfl)

public def BitVecBasis (n : ℕ) :
  (BasisRegister.MulTensor (Fin n) (fun _ => QubitSpace)).indexing ≃ (List.Vector Bool n) :=
  Equiv.trans
  (Equiv.arrowCongr (Equiv.refl (Fin n)) QubitIndexingAsBool) -- Fin n → Fin 2 ≃ Fin n → Bool
  ((Equiv.vectorEquivFin Bool n).symm)

public instance {n : ℕ} : Coe (List.Vector Bool n) (BasisRegister.MulTensor (Fin n) (fun _ => QubitSpace)).indexing where
  coe := (BitVecBasis n).symm

public instance {n : ℕ} : Coe (BasisRegister.MulTensor (Fin n) (fun _ => QubitSpace)).indexing (List.Vector Bool n) where
  coe := (BitVecBasis n)

public instance {n : ℕ} : Coe (BitVec n) (List.Vector Bool n) where
  coe := fun bv => List.Vector.ofFn (fun (i : Fin n) => bv[i])

notation "(" k ")" "|" n "⟩" => List.Vector.ofFn (fun (i : Fin k) => (BitVec.ofNat k n)[i])

public noncomputable abbrev QubitZeroState (n : ℕ) : BasisStateSpace (BasisRegister.MulTensor (Fin n) (fun _ => QubitSpace))
  := GetBasisState (n)|0⟩

-- #check (5)|0b111⟩

end BitStringIndexing
