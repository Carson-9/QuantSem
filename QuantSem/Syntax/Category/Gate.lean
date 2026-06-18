/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import QuantSem.Syntax.Category.Register
public import QuantSem.Syntax.Category.State
public import QuantSem.Syntax.Category.QuantumTypes

namespace SyntacticGate


open SyntacticRegister
open SyntacticState
open QuantumTypes
open CategoryTheory
open ContinuousLinearMap

public abbrev QuantumGate (R1 R2 : TypeQuantumRegister) : Type :=  R1 ⟶ R2
public abbrev TypeQuantumGate := Σ E : TypeQuantumRegister, Σ F : TypeQuantumRegister, QuantumGate E F

public abbrev TypeQuantumGate.entrySpace (g : TypeQuantumGate) := g.fst
public abbrev TypeQuantumGate.exitSpace (g : TypeQuantumGate) := g.snd.fst
public abbrev TypeQuantumGate.gate (g : TypeQuantumGate) := g.snd.snd


public noncomputable def GateTensor {R1 R2 R3 R4 : TypeQuantumRegister}
  (g1 : QuantumGate R1 R2) (g2 : QuantumGate R3 R4)
  : QuantumGate (R1 ⊗ᵣ R3) (R2 ⊗ᵣ R4) := g1 ⊗ₕ g2

public noncomputable def GateTensor' (g1 g2 : TypeQuantumGate) : TypeQuantumGate :=
  ⟨g1.entrySpace ⊗ᵣ g2.entrySpace, ⟨g1.exitSpace ⊗ᵣ g2.exitSpace ,
    @GateTensor g1.entrySpace g1.exitSpace g2.entrySpace g2.exitSpace g1.gate g2.gate ⟩⟩

notation g1 "⊗ₚ" g2 => GateTensor' g1 g2


public noncomputable def GateComp {R1 R2 R3 : TypeQuantumRegister}
  (g1 : QuantumGate R1 R2) (g2 : QuantumGate R2 R3) : QuantumGate R1 R3 :=
  g1 ≫ g2

public noncomputable def GateComp' (g1 g2 : TypeQuantumGate) (h : g1.exitSpace ≅ g2.entrySpace)
  : TypeQuantumGate :=
  ⟨g1.entrySpace, ⟨g2.exitSpace, g1.gate ≫ h.hom ≫ g2.gate ⟩⟩


notation g1 "-<" R ">-" g2 => GateComp' g1 g2 (Iso.refl R)

/-
    Gates can update states
-/

public noncomputable abbrev GateStateEvolve (g : TypeQuantumGate) (s : QuantumStateSpace g.entrySpace)
  : QuantumStateSpace g.exitSpace := s ≫ g.gate

public noncomputable abbrev GateStateEvolve' (g : TypeQuantumGate) (s : QuantumStateSpace g.entrySpace)
  : TypeQuantumState := ⟨g.exitSpace, GateStateEvolve g s⟩

public noncomputable def GateStateEvolve'' (g : TypeQuantumGate) (s : TypeQuantumState)
  (h : s.space ≅ g.entrySpace) : TypeQuantumState :=
  ⟨g.exitSpace, s.state ≫ h.hom ≫ g.gate⟩

notation g "[" R "/" s "]" => GateStateEvolve'' g s (Iso.refl R)


/-
    Theorems on gate state evolution
-/

@[simp]
public theorem GateCompositionCommutation {R1 R2 R3 R4 R5 R6 : TypeQuantumRegister}
  (g11 : QuantumGate R1 R2) (g12 : QuantumGate R2 R3)
  (g21 : QuantumGate R4 R5) (g22 : QuantumGate R5 R6) :
  GateTensor (g11 ≫ g12) (g21 ≫ g22) = (GateTensor g11 g21) ≫ (GateTensor g12 g22) :=
  by unfold GateTensor; rw [<-tensor_factorises]

@[simp]
public theorem GateId (R : TypeQuantumRegister) :
  ∀ s : QuantumStateSpace R, GateStateEvolve (⟨R, ⟨R, id_map R⟩⟩) s = s :=
  by intro s; unfold GateStateEvolve; apply id_map_is_neutral_right

/-
    Gate Extensionality --- /!\ THIS IS NOT TRUE IN HIGHER ORDER LOGIC!
    --> The unit sphere cannot be proven to be a generating set, as this
    would prove that every module has a generating set, which would prove
    the axiom of choice and thus the Law of excluded middle

    This is not surprising, as π₀(ℂ) and π₀(ℂ*) are not isomorphic, but π₀(ℂ) ↪ π₀(ℂ*)
    (See univalent foundations for more intuition)
-/

@[ext]
public theorem GateExtTotalSpace {R1 R2 : TypeQuantumRegister} (g1 g2 : QuantumGate R1 R2) :
  (∀ x : R1.space, (g1.toFun x) = (g2.toFun x)) → (g1 = g2) :=
  by intro h; apply LinearIsometry.ext; exact h

@[ext]
public axiom GateExtUnitVectors {R1 R2 : TypeQuantumRegister} (g1 g2 : QuantumGate R1 R2) :
  (∀ x : R1.space, ‖x‖ = 1 → (g1.toFun x) = (g2.toFun x)) → (g1 = g2)
  -- := by intro h; apply GateExtTotalSpace; intro x; sorry
  -- calc
  -- g1.toFun x = ‖‖
  -- apply (h (NormalizeElement x) (NormOfNormalizedIsOne x))

@[ext]
public axiom GateExtUnitary {R1 R2 : TypeQuantumRegister} (g1 g2 : QuantumGate R1 R2) :
  (∀ s : QuantumStateSpace R1, (s ≫ g1) = (s ≫ g2)) → (g1 = g2)
  -- := by intro h; ext x; sorry
  -- calc
  -- g1.toFun x = g1.toFun ((1 : ℂ) • x) := by simp
  -- _ = g1.toFun ((‖x‖ * ‖x‖⁻¹) • x) := by rw[<- Field.mul_inv_cancel ‖x‖]
  -- _ = g1.toFun (‖x‖ • (‖x‖⁻¹ • x)) := by simp
  -- _ = ‖x‖ • g1.toFun (‖x‖⁻¹ • x) := by simp
  -- _ = ‖x‖ • g2.toFun (‖x‖⁻¹ • x) := by simp
  -- _ = g2.toFun ((‖x‖ • ‖x‖⁻¹) • x) := by simp
  -- _ = g2.toFun (1 • x) := by simp
  -- _ = g2.toFun x := by simp

-- LinearIsometry.map_smul

public theorem GateEqImpliesStateEvolve {R1 R2 : TypeQuantumRegister} (g1 g2 : QuantumGate R1 R2)
  : (g1 = g2) → ∀ s : QuantumStateSpace R1, (s ≫ g1) = (s ≫ g2) :=
  by intro h; rw[h]; intro s; rfl

public theorem GateExtIff {R1 R2 : TypeQuantumRegister} (g1 g2 : QuantumGate R1 R2)
  : (g1 = g2) ↔ ∀ s : QuantumStateSpace R1, (s ≫ g1) = (s ≫ g2) :=
  by apply Iff.intro; intro h; rw[h]; intro s; rfl; apply GateExtUnitary


end SyntacticGate
