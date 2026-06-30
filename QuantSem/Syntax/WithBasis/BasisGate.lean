/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import QuantSem.Syntax.WithBasis.FinSuppBasisTypes
public import QuantSem.Syntax.WithBasis.BasisRegister
public import QuantSem.Syntax.WithBasis.BasisState
public import QuantSem.Syntax.Category.Gate
public import QuantSem.Syntax.Category.State

namespace BasisGate


open SyntacticGate
open BasisTypes
open BasisRegister
open BasisState
open QuantumTypes
open CategoryTheory


public abbrev BasisGateType (R1 R2 : TypeBasisRegister) : Type :=  QuantumGate (BasisRegToQuantReg R1) (BasisRegToQuantReg R2)
public abbrev TypeBasisGate := Σ R1, Σ R2, BasisGateType R1 R2


/-
    Gate Extensionality with basis
-/

@[ext]
public theorem GateExtBasis {R1 R2 : TypeBasisRegister} (g1 g2 : BasisGateType R1 R2) :
  (∀ i : R1.indexing , ((GetBasisState i) ≫ g1) = ((GetBasisState i) ≫ g2)) → (g1 = g2) :=
  by intro hyp
     apply @LinearIsometryBasisExt R1.space R2.space R1.indexing R2.indexing R1.struct R2.struct g1 g2;
     intro i; specialize hyp i;
     rw[<- GetBasisStateAtOne i]
     rw[QuantumTypes.LinearIsometriesOnCAgree] at hyp
     simp at hyp; apply hyp

public theorem GateExtBasisIff {R1 R2 : TypeBasisRegister} (g1 g2 : BasisGateType R1 R2) :
   (g1 = g2) ↔ (∀ i : R1.indexing , ((GetBasisState i) ≫ g1) = ((GetBasisState i) ≫ g2)):=
  by apply Iff.intro; intro hyp; rw[hyp]; intro i; rfl; apply GateExtBasis

public noncomputable def GateFromBasis {R1 R2 : TypeBasisRegister} (f : R1.indexing → BasisStateSpace R2)
  (hOrth : Orthonormal ℂ (fun i => (f i).toFun (1 / (‖(1 : ℂ)‖) : ℂ))) : BasisGateType R1 R2 :=
  LinearIsometryFromBasis R1.space R2.space R1.indexing R2.indexing (fun i => (f i).toFun (1 / (‖(1 : ℂ)‖) : ℂ))
  (hOrth)

/-
    Id Gate
-/

public abbrev IdGate (R : TypeBasisRegister) : BasisGateType R R := SyntacticRegister.CatRegister.id (BasisRegToQuantReg R)

/-
    Control Gates
-/

public noncomputable def ControlGate  {R1 R2 : TypeBasisRegister} (control : R1.indexing → BasisGateType R2 R2) :
  BasisGateType (R1 ⊗ᵣ R2) (R1 ⊗ᵣ R2) :=
  GateFromBasis (fun (i, j) => (⟨R1, (GetBasisState i)⟩ ⊗ₛ ⟨R2, (GetBasisState j) ≫ (control i)⟩).snd ) --(R1.struct.toBasis i) ⊗ₜ[ℂ] ((control i).toFun (R2.struct.toBasis j)))
  (by unfold Orthonormal; apply And.intro; intro i; simp; sorry;
      simp; intro i j h; rcases i with ⟨fsti, sndi⟩; simp; rcases j with ⟨fstj, sndj⟩;
        simp; --rw[RCLike.inner_tmul_eq]
        sorry
  )


end BasisGate
