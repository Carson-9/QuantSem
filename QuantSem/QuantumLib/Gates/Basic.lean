/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import QuantSem.QuantumLib.Registers.Basic
public import QuantSem.QuantumLib.States.Basic
public import QuantSem.QuantumLib.HilbertSpaces.Basic

namespace SyntacticGate


open SyntacticRegister
open SyntacticState
open QuantumTypes
open CategoryTheory
open ContinuousLinearMap

public abbrev QuantumGate (R1 R2 : QuantumRegister) : Type :=  R1 ⟶ R2

public noncomputable abbrev GateTensor {R1 R2 R3 R4 : QuantumRegister}
  (g1 : QuantumGate R1 R2) (g2 : QuantumGate R3 R4) : QuantumGate (R1 ⊗ᵣ R3) (R2 ⊗ᵣ R4) := g1 ⊗ₕ g2

notation g1 "⊗ₚ" g2 => GateTensor g1 g2


public noncomputable def GateComp {R1 R2 R3 : QuantumRegister}
  (g1 : QuantumGate R1 R2) (g2 : QuantumGate R2 R3) : QuantumGate R1 R3 := g1 ≫ g2

public abbrev IdGate (R : QuantumRegister) : QuantumGate R R := QuantumRegisterCat.id R

/-
    Gates can update states
-/

public noncomputable abbrev GateStateEvolve {R1 R2 : QuantumRegister} (g : QuantumGate R1 R2)
  (s : QuantumStateSpace R1) : QuantumStateSpace R2 := s ≫ g

/-
    Theorems on gate state evolution
-/

@[simp]
public theorem GateCompositionCommutation {R1 R2 R3 R4 R5 R6 : QuantumRegister}
  (g11 : QuantumGate R1 R2) (g12 : QuantumGate R2 R3)
  (g21 : QuantumGate R4 R5) (g22 : QuantumGate R5 R6) :
  GateTensor (g11 ≫ g12) (g21 ≫ g22) = (GateTensor g11 g21) ≫ (GateTensor g12 g22) :=
  by unfold GateTensor; rw [<-tensor_factorises]

@[simp]
public theorem GateId (R : QuantumRegister) :
  ∀ s : QuantumStateSpace R, GateStateEvolve (IdGate R) s = s :=
  by intro s; unfold GateStateEvolve; apply id_map_is_neutral_right

/-
    Gate Extensionality --- /!\ THE EXPECTED EXTENSIONNALITY OVER STATES
    IS NOT TRUE (A priori) IN HIGHER ORDER LOGIC!
    --> The unit sphere cannot be proven to be a generating set, as this
    would prove that every module has a generating set, which would prove
    the axiom of choice and thus the Law of excluded middle

    This is not surprising, as π₀(ℂ) and π₀(ℂ*) are not isomorphic, but π₀(ℂ) ↪ π₀(ℂ*)
    (See univalent foundations for more intuition)
-/

@[ext]
public theorem GateExtTotalSpace {R1 R2 : QuantumRegister}
  (g1 g2 : QuantumGate R1 R2) : (∀ x : R1.space, (g1.toFun x) = (g2.toFun x)) → (g1 = g2) :=
  by intro h; apply LinearIsometry.ext; exact h


public theorem GateEqImpliesStateEvolve {R1 R2 : QuantumRegister} (g1 g2 : QuantumGate R1 R2)
  : (g1 = g2) → ∀ s : QuantumStateSpace R1, (s ≫ g1) = (s ≫ g2) :=
  by intro h; rw[h]; intro s; rfl


/-
    Gates over PiTensorProducts
    -- Mathlib not developped enough yet
-/

-- public def SyntacticGate.MulTensor {I : Type} {H : I → QuantumRegister}
--   (gFam : (i : I) → QuantumGate (H i) (H i)) : QuantumGate (QuantumRegister.MulTensor I H) (QuantumRegister.MulTensor I H)
--   := PiTensorProduct.map gFam



end SyntacticGate
