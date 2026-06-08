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

variable (M N : Type) [FinDimReg M] [FinDimReg N]

@[expose]
public def FinDimGate : Type :=  M →ₗᵢ[ℂ] N
public abbrev TypeFinDimGate := Σ E : TypeFinRegister, Σ E' : TypeFinRegister,
  @FinDimGate E.fst E'.fst E.snd E'.snd

@[expose, coe]
public def FinDimGateAsGate (g : TypeFinDimGate) : TypeQuantumGate :=
  ⟨ FinRegAsRegFun g.fst, ⟨ FinRegAsRegFun g.snd.fst, g.snd.snd ⟩ ⟩

public def MatrixToFinDimGate (Mat : Matrix (Fin (FinDimReg.dim M)) (Fin (FinDimReg.dim N)) ℂ)
  [LinearIsometry (Matrix.toLin Mat)] : FinDimGate M N
  := Matrix.toLin Mat

public def FinDimGateToMatrix (g : FinDimGate M N) : Matrix (Fin (FinDimReg.dim M)) (Fin (FinDimReg.dim N)) ℂ :=
  fun i j => (QuantReg.inner N) (N.basis i) (M (M.basis j))


end FinDimGates
