/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import QuantSem.Syntax.HighLevelInstance.HighLevelInstance
public import Mathlib.Logic.Function.Defs

open QuantumTypes
open SyntacticRegister
namespace FinDimRegisters

public class FinDimReg (E : Type) extends QuantReg E, FiniteDimensional ℂ E where
  dim : ℕ
  computationalBasis : Fin dim → E
  orthogonalBasis : ∀ i j : Fin dim, inner (computationalBasis i) (computationalBasis j) = 0
  normalBasis : ∀ i : Fin dim, ‖computationalBasis i‖ = 1
  basisDecomp (v : E) (i : Fin dim) : ℂ := inner v (computationalBasis i)
  isDecomp (v : E) : (∑ i : Fin dim, (basisDecomp v i) • (computationalBasis i)) = v
  decompUnique (v : E) (f : Fin dim → ℂ) (h : (∑ i : Fin dim, (f i) • (computationalBasis i)) = v)
    : f = (basisDecomp v)
    -- Could be proven here once theory of finite dimensional hilbert spaces is developped


public abbrev TypeFinRegister := Σ E, FinDimReg E

@[expose, coe]
public def FinRegAsRegFun (R : TypeFinRegister) : TypeQuantumRegister :=
  ⟨ R.fst, R.snd.toQuantReg ⟩

@[default_instance 101]
instance FinRegAsReg : Coe TypeFinRegister TypeQuantumRegister where
  coe := FinRegAsRegFun

notation "|" i "⟩" => FinDimReg.basis i


-- Cannot extend the existing algebra on register as it must preserve it's finite
-- dimensional property
public class FiniteDimRegTensorAlgebra extends Monoid TypeFinRegister where
  mul := Mul.mul
  basisFactorization (E F : TypeFinRegister) :
    (Fin E.snd.dim) × (Fin F.snd.dim) → Fin (mul E F).snd.dim
  factorizationBij (E F : TypeFinRegister) : Function.Bijective (basisFactorization E F)



end FinDimRegisters
