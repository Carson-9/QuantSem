/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import QuantSem.QuantumLib.HilbertSpaces.AbstractBasis
--public import QuantSem.QuantumLib.Registers.PiAbstractBasis
public import QuantSem.QuantumLib.Registers.AbstractBasis
public import QuantSem.QuantumLib.States.AbstractBasis
public import QuantSem.QuantumLib.Gates.Basic
public import QuantSem.QuantumLib.States.Basic

namespace BasisGate


open SyntacticGate
open BasisTypes
--open PiBasisRegister
open AbstractBasisRegister
open BasisState
open QuantumTypes
open CategoryTheory


public abbrev BasisGateType (R1 R2 : BasisRegister) : Type := QuantumGate R1 R2

/-
    Gate Extensionality with basis
-/

@[ext]
public theorem GateExtBasis {R1 R2 : BasisRegister} (g1 g2 : BasisGateType R1 R2) :
  (∀ i : R1.indexing , ((GetBasisState i) ≫ g1) = ((GetBasisState i) ≫ g2)) → (g1 = g2) :=
  by intro hyp
     apply @LinearIsometryBasisExt R1.space R2.space R1.indexing R2.indexing R1.struct R2.struct g1 g2;
     intro i; specialize hyp i;
     rw[<- GetBasisStateAtOne i]
     rw[QuantumTypes.LinearIsometriesOnCAgree] at hyp
     simp at hyp; apply hyp

public theorem GateExtBasisIff {R1 R2 : BasisRegister} (g1 g2 : BasisGateType R1 R2) :
   (g1 = g2) ↔ (∀ i : R1.indexing , ((GetBasisState i) ≫ g1) = ((GetBasisState i) ≫ g2)):=
  by apply Iff.intro; intro hyp; rw[hyp]; intro i; rfl; apply GateExtBasis

public noncomputable def GateFromBasis {R1 R2 : BasisRegister} (f : R1.indexing → BasisStateSpace R2)
  (hOrth : Orthonormal ℂ (fun i => (f i).toFun (1 : ℂ))) : BasisGateType R1 R2 :=
  LinearIsometryFromBasis (fun i => (f i).toFun (1 : ℂ)) (hOrth)

/-
    Applying a gate to an orthonormal family yields an orthonormal family
-/

public theorem GateEvolveOrthonormal {R1 R2 : BasisRegister}
  {I : Type} (f : I → BasisStateSpace R1) (g : BasisGateType R1 R2)
  (hOrth : Orthonormal ℂ (fun i => (f i).toFun (1 : ℂ)))
  : Orthonormal ℂ (fun i => (GateStateEvolve g (f i)).toFun (1 : ℂ)) :=
  by simp; unfold Orthonormal; apply And.intro; intro i; simp; rw[ComplexNormOfOne];
      simp; apply hOrth.right


/-
    Control Gates over a Family of wires
    -- Mathlib not developped enough yet
-/

public noncomputable instance {R : BasisRegister} : Coe (BasisGateType R R) (BasisGateType (⨂ᵣ [R]) (⨂ᵣ [R])) where
  coe := fun g =>  GateFromBasis (fun i => (@GateStateEvolve R R g (@GetBasisState R (i 0)))) (by simp; sorry)

-- PiTensorProduct.singleAlgHom

-- public noncomputable def DirtySingleControlGate (I : Type) [Finite I] (H : I → BasisRegister)
--   (controlWire controlGate : I) (hDiff : controlWire ≠ controlGate)
--   (controlEffect : (H controlWire).indexing → BasisGateType (H controlGate) (H controlGate))
--   : BasisGateType (BasisRegister.MulTensor I H) (BasisRegister.MulTensor I H) :=
--   GateFromBasis (fun i_prod => -- (i_prod controlWire)
--
--   GetBasisState i_prod) (by sorry)

-- public noncomputable def DirtyControlGate (I : Type) [Finite I] (H : I → BasisRegister)
--   {ιGate ιWire : Type} [Finite ιGate] [Finite ιWire]
--   (GateIndexing : ιGate → I) (WireIndexing : ιWire → I)
--   (controlEffect :
--   (BasisRegister.MulTensor ιWire (fun i => (H (WireIndexing i)))).indexing →
--     (BasisGateType (BasisRegister.MulTensor ιGate (fun i => H (GateIndexing i))) (BasisRegister.MulTensor ιGate (fun i => H (GateIndexing i)))))
--   : BasisGateType (BasisRegister.MulTensor I H) (BasisRegister.MulTensor I H) :=
--   by sorry


-- public noncomputable def ControlGate  {R1 R2 : BasisRegister} (control : R1.indexing → BasisGateType R2 R2) :
--   BasisGateType (R1 ⊗ᵣ R2) (R1 ⊗ᵣ R2) :=
--   GateFromBasis (fun (i, j) => (⟨R1, (GetBasisState i)⟩ ⊗ₛ ⟨R2, (GetBasisState j) ≫ (control i)⟩).snd ) --(R1.struct.toBasis i) ⊗ₜ[ℂ] ((control i).toFun (R2.struct.toBasis j)))
--   (by simp; unfold Orthonormal; apply And.intro; intro i; simp; rw[NormInTensorUnit]; simp;
--       simp; intro i j h; rcases i with ⟨fsti, sndi⟩; simp; rcases j with ⟨fstj, sndj⟩;
--         simp;  --rw[RCLike.inner_tmul_eq]
--         sorry
--   )

--public noncomputable def SwapGate {R : List TypeBasisRegister} (i j : Fin (R.length)) :
--  BasisGateType (⨂ᵣ R) (⨂ᵣ R) :=
--  GateFromBasis
--     _ _


public def BasisGateMulTensor {I : Type} [Finite I] {H : I → BasisRegister}
  (gFam : (i : I) → BasisGateType (H i) (H i)) : BasisGateType (BasisRegister.MulTensor I H) (BasisRegister.MulTensor I H)
  := by sorry -- (GateMulTensor gFam)

--@[find_better]
public noncomputable def DirtyControlGate (l : List BasisRegister)
  (controlWire controlledGate : Fin l.length)
  (actualGateFam : (l.get controlWire).indexing → BasisGateType (l.get controlledGate) (l.get controlledGate))
  : BasisGateType (BasisRegister.MulTensor (Fin l.length) l.get) (BasisRegister.MulTensor (Fin l.length) l.get) :=
  GateFromBasis
    (fun i => (GateStateEvolve
      (BasisGateMulTensor
        (fun k : Fin l.length => if heq : k = controlledGate
          then by rw[heq]; apply (actualGateFam (i controlWire))
          else (IdGate (l.get k))))
      (GetBasisState i))
    )
    (by sorry)



end BasisGate
