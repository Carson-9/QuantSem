/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import Mathlib.CategoryTheory.Monoidal.Category
public import QuantSem.QuantumLib.Registers.Basic

open SyntacticRegister QuantumTypes
open CategoryTheory

namespace SyntacticState

/-
    A State is represented as a Morphism S : ℂ ⟶ R, where the "actual" content is S(1 / ‖1‖)
 -/

public abbrev QuantumStateSpace (R : QuantumRegister) : Type := QuantumRegisterMonCat.tensorUnit ⟶ R


public noncomputable def QuantumStateTensor {R1 R2 : QuantumRegister} (S1 : QuantumStateSpace R1)
  (S2 : QuantumStateSpace R2) : QuantumStateSpace (R1 ⊗ᵣ R2) :=
  ((QuantumRegisterMonCat.leftUnitor QuantumRegisterMonCat.tensorUnit).inv ≫ (S1 ⊗ₕ S2))

notation S1 "⊗ₛ" S2 => QuantumStateTensor S1 S2

@[expose]
public noncomputable def QuantumStateSelection {R : QuantumRegister}
  (x : R.space) (hNorm : ‖x‖ = 1) : QuantumStateSpace R :=
  ElementInSpaceAsIso x (by intro hAbs; rw[hAbs] at hNorm; rw[norm_zero] at hNorm; apply zero_ne_one at hNorm; apply hNorm)

@[simp]
public theorem StateSelectionOfOne  {R : QuantumRegister} (x : R.space) (hNorm : ‖x‖ = 1) :
  (QuantumStateSelection x hNorm).toFun (1 : ℂ) = x := by unfold QuantumStateSelection; rw[ElementInSpacePointsTo]; rw[hNorm]; simp

@[simp]
public theorem StateExtAtOne {R : QuantumRegister} (x y : R.space) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  : (QuantumStateSelection x hx).toFun (1 : ℂ) = (QuantumStateSelection y hy).toFun (1 : ℂ)
    → (QuantumStateSelection x hx) = (QuantumStateSelection y hy) :=
  by intro hyp; unfold QuantumStateSelection; apply LinearIsometry.ext; intro z;
     unfold ElementInSpaceAsIso; simp; simp at hyp; rw [hyp];

public theorem StateEqualAreAtOne {R : QuantumRegister} (x y : R.space) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  : (QuantumStateSelection x hx) = (QuantumStateSelection y hy) →
    (QuantumStateSelection x hx).toFun (1 : ℂ) = (QuantumStateSelection y hy).toFun (1 : ℂ)
  := by intro hyp; rw[hyp]



/-
    True extensionality for states
-/

@[ext]
public theorem StateExt {R : QuantumRegister} (s1 s2 : QuantumStateSpace R) :
  s1.toFun (1 : ℂ) = s2.toFun (1 : ℂ) → s1 = s2 :=
  by rw[LinearIsometriesOnCAgree' s1 s2]; intro h; apply h

/-
    States are "unitaries"
-/

public theorem StateNormAtOne {R : QuantumRegister} (s : QuantumStateSpace R) :
  ‖s.toFun (1 : ℂ)‖ = ‖(1 : ℂ)‖ := by apply LinearIsometry.norm_map


/-
    Induction principle for states over a tensor
-/

--public theorem StateTensorInduction {R1 R2 : QuantumRegister}
--  (p : (QuantumStateSpace (R1 ⊗ᵣ R2)) → Prop)
--  (hAllBasis : ∀ x1 : QuantumStateSpace R1, ∀ x2 : QuantumStateSpace R2, p (x1 ⊗ₛ x2)) :
--  ∀ x : (QuantumStateSpace (R1 ⊗ᵣ R2)), p x :=
--  by

-- public noncomputable def QuantumState.MulTensor (I : Type) (H : I → QuantumRegister)
--   (S : (i : I) → QuantumStateSpace (H i)) : QuantumStateSpace (QuantumRegister.MulTensor I H)
--   := PiTensorProduct.tprod ℂ



end SyntacticState
