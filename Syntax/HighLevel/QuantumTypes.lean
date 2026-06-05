module


public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

open ContinuousLinearMap InnerProductSpace
open scoped InnerProduct ComplexInnerProductSpace

namespace QuantumTypes

public class QuantumType (E : Type) extends NormedAddCommGroup E, InnerProductSpace ℂ E
@[expose]
public def TypeQuantumTypes : Type 1 := Σ E, QuantumType E

end QuantumTypes
