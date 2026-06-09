/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import QuantSem.Syntax.HighLevelInstance.HighLevelInstance
public import QuantSem.Syntax.FinDim.FinDimRegister
public import QuantSem.Syntax.FinDim.FinDimState

open FinDimRegisters
open FinDimStates
open SyntacticGate
namespace FinDimGates

variable (M N : Type) [M' : FinDimReg M] [N' : FinDimReg N]

@[expose]
public def FinDimGate : Type :=  M →ₗᵢ[ℂ] N
public abbrev TypeFinDimGate := Σ E : TypeFinRegister, Σ E' : TypeFinRegister,
  @FinDimGate E.fst E'.fst E.snd E'.snd

@[expose, coe]
public def FinDimGateAsGate (g : TypeFinDimGate) : TypeQuantumGate :=
  ⟨ FinRegAsRegFun g.fst, ⟨ FinRegAsRegFun g.snd.fst, g.snd.snd ⟩ ⟩

public noncomputable def MatrixToFinDimGate
  (Mat : Matrix (Fin (FinDimReg.dim N)) (Fin (FinDimReg.dim M)) ℂ) (h : ∀ x : M,
    N'.norm
      ((Matrix.toLin
        (@FinDimReg.computationalBasis M M')
        (@FinDimReg.computationalBasis N N') Mat) x)
    = (M'.norm x)) : FinDimGate M N
  :=
  LinearIsometry.mk
    (Matrix.toLin (@FinDimReg.computationalBasis M M') (@FinDimReg.computationalBasis N N') Mat)
    (by intro x; apply (h x) )

public noncomputable def FinDimGateToMatrix (g : FinDimGate M N)
  : Matrix (Fin (FinDimReg.dim N)) (Fin (FinDimReg.dim M)) ℂ :=
  LinearMap.toMatrix
    (@FinDimReg.computationalBasis M M')
    (@FinDimReg.computationalBasis N N')
    g.toLinearMap

public noncomputable def FinDimGateToBasisChar (g : FinDimGate M N) : Fin M'.dim → N :=
  fun i => g.toLinearMap (M'.computationalBasis i)

  -- ComputationalBasis.repr v gives the function representing v in this basis !

-- public def GateOnBasisCharacterization (g : FinDimGate M N)
--  (onBasis : Fin M'.dim → N) (s : FinDimStateSpace M) : FinDimStateSpace N :=
--  _

end FinDimGates
