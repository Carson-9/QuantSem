/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module

public import QuantSem.Syntax.Category.Circuit
public import QuantSem.Syntax.Category.CircuitComplexity

open SyntacticRegister
open SyntacticState
open SyntacticGate
open SyntacticCircuit
open SyntacticCircuitComplexity

namespace SyntacticCircuitTactic

open SimpleCircuitOverRegister

/-
    Circuit "Syntactic" Normal Form
    Since one does not have access to true computational content on gate composition,
    this normal form relies only on the shape of the circuit, trying to push
    vertical compositions at the top.
    Later, this normal form will be Gate (SimpleCircuitGateRepr)
-/


public def SimpleCircuitRemoveIdWire {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R) :
  SimpleCircuitOverRegister R := match c with
  | IdWire => IdWire -- If IdWire is the whole circuit, must keep it
  | RegisterSwap iso c =>  RegisterSwap iso (SimpleCircuitRemoveIdWire c)
  | Gate g => Gate g
  | HorizontalComp c1 c2 => match (SimpleCircuitRemoveIdWire c1) with
        | IdWire => SimpleCircuitRemoveIdWire c2
        | _ => match (SimpleCircuitRemoveIdWire c2) with
          | IdWire => SimpleCircuitRemoveIdWire c1
          | _ => HorizontalComp (SimpleCircuitRemoveIdWire c1) (SimpleCircuitRemoveIdWire c2)
  | VerticalComp c1 c2 => VerticalComp (SimpleCircuitRemoveIdWire c1) (SimpleCircuitRemoveIdWire c2)

public theorem RemoveIdWireEquiv {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R)
  : c ≅ₖ SimpleCircuitRemoveIdWire c
  := by induction c with
    | IdWire => unfold SimpleCircuitRemoveIdWire; apply CircuitEquivalenceRefl
    | RegisterSwap iso c ic => unfold SimpleCircuitRemoveIdWire; unfold CircuitEquivalence; _
    | Gate g => unfold SimpleCircuitRemoveIdWire; apply CircuitEquivalenceRefl
    | HorizontalComp c1 c2 c1ih c2ih =>
        unfold SimpleCircuitRemoveIdWire
        split
        case _ heq => apply CircuitEquivalenceTrans; rw[heq] at c1ih; apply HorizontalRewriteLeft c1 IdWire c2 c1ih; apply CircuitEquivalenceTrans; apply IdWireIsIdLeft; apply c2ih
        case _ _ =>
          split
          case _ heq =>  apply CircuitEquivalenceTrans; rw[heq] at c2ih; apply HorizontalRewriteRight c1 c2 IdWire c2ih; apply CircuitEquivalenceTrans; apply IdWireIsIdRight; apply c1ih
          case _ => apply CircuitEquivalenceTrans; apply HorizontalRewriteLeft c1 (SimpleCircuitRemoveIdWire c1) c2 c1ih; apply HorizontalRewriteRight (SimpleCircuitRemoveIdWire c1) c2 (SimpleCircuitRemoveIdWire c2) c2ih;
    | VerticalComp c1 c2 c1ih c2ih => unfold SimpleCircuitRemoveIdWire; apply CircuitEquivalenceTrans _ _ _ (ParallelRewriteUp c1 (SimpleCircuitRemoveIdWire c1) c2 c1ih) (ParallelRewriteDown  (SimpleCircuitRemoveIdWire c1) c2  (SimpleCircuitRemoveIdWire c2) c2ih)



/-
public def SimpleCircuitParenthesisNF {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R) :
  SimpleCircuitOverRegister R := match c with
  | IdWire => IdWire
  | Gate g => Gate g
  | VerticalComp (HorizontalComp c1' c1'') (HorizontalComp c2' c2'') =>  HorizontalComp
            (SimpleCircuitParenthesisNF (VerticalComp c1' c2'))
            (SimpleCircuitParenthesisNF (VerticalComp c1'' c2''))
  | VerticalComp c1 c2 => VerticalComp (SimpleCircuitParenthesisNF c1) (SimpleCircuitParenthesisNF c2)
  | HorizontalComp c1 c2 => HorizontalComp (SimpleCircuitParenthesisNF c1) (SimpleCircuitParenthesisNF c2)
termination_by (SimpleCircuitDepth c)
decreasing_by sorry; sorry; sorry; sorry; sorry; sorry -- unfold SimpleCircuitDepth; simp;



public theorem SimpleCircuitParenthesisNFEquiv {R : TypeQuantumRegister} (c : SimpleCircuitOverRegister R) :
  c ≅ₖ SimpleCircuitParenthesisNF c :=
  by induction c with
  | IdWire => unfold SimpleCircuitParenthesisNF; apply CircuitEquivalenceRefl
  | Gate g => unfold SimpleCircuitParenthesisNF; apply CircuitEquivalenceRefl
  | HorizontalComp c1 c2 c1h c2h => unfold SimpleCircuitParenthesisNF; apply CircuitEquivalenceTrans _ _ _ (HorizontalRewriteLeft c1 (SimpleCircuitParenthesisNF c1) c2 c1h) (HorizontalRewriteRight  (SimpleCircuitParenthesisNF c1) c2 (SimpleCircuitParenthesisNF c2) c2h)
  | VerticalComp c1 c2 c1h c2h =>
    unfold SimpleCircuitParenthesisNF
    case _ => _
    --case _ => apply CircuitEquivalenceTrans _ _ _ (ParallelRewriteUp c1 (SimpleCircuitParenthesisNF c1) c2 c1h) (ParallelRewriteDown  (SimpleCircuitParenthesisNF c1) c2 (SimpleCircuitParenthesisNF c2) c2h)
-/

-- Cannot affirm the property of normal forms, as Gate (id_map) and IdWire are equivalent
-- without having the same parenthesis NF
