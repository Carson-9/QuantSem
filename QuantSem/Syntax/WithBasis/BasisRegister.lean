/-
Copyright (c) 2026 William Hasley. All rights reserved.
Released under GNU GPL3 license as described in the file LICENSE.
Authors: William Hasley
-/


module


public import QuantSem.Syntax.WithBasis.FinSuppBasisTypes
public import QuantSem.Syntax.Category.Register
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Monoidal.Subcategory

namespace BasisRegister

open SyntacticRegister
open BasisTypes
open Monoid
open CategoryTheory

/-
Quantum registers depend on Quantum Type composition.
Often, the given composition will be the Tensor product of hilbert spaces
-/

--public abbrev QuantumRegister := TypeQuantumTypes
public abbrev BasisReg (R : Type) (ι : Type) := BasisTypes.HilbertSpaceWithBasis R ι
public abbrev TypeBasisRegister := Σ E, (Σ ι, BasisReg E ι)

public abbrev TypeBasisRegister.space (R : TypeBasisRegister) := R.fst
public abbrev TypeBasisRegister.indexing (R : TypeBasisRegister) := R.snd.fst
public abbrev TypeBasisRegister.struct (R : TypeBasisRegister) := R.snd.snd

@[coe, expose]
public def BasisRegToQuantReg (R : TypeBasisRegister) : TypeQuantumRegister :=
  ⟨R.space, R.struct.toHilbertSpace⟩

instance : Coe TypeBasisRegister TypeQuantumRegister where
  coe := BasisRegToQuantReg

@[default_instance]
public instance (R : TypeBasisRegister) : HilbertSpaceWithBasis R.space R.indexing :=
  R.struct

@[expose, coe]
public def BasisRegToTypeBasisRegister (R ι : Type) [R' : BasisReg R ι] :
  TypeBasisRegister := ⟨R, ⟨ι, R'⟩⟩

@[expose, coe, reducible]
public def TypeBasisRegToStruct (R : TypeBasisRegister) : BasisReg R.space R.indexing := R.struct

/-
    The (Category-theory) property of having a basis
-/

public abbrev QuantumRegHasBasis (R : TypeQuantumRegister) : Prop :=
  ∃ ι : Type, ∃ b : (Module.Basis ι ℂ R.space), Orthonormal ℂ (fun i => b i)


@[default_instance]
public noncomputable instance QuantRegToBasis (R : TypeQuantumRegister) (p : QuantumRegHasBasis R) : HilbertSpaceWithBasis R.space p.choose where
  repr := p.choose_spec.choose.repr
  isOrthonormal := p.choose_spec.choose_spec

@[coe]
public noncomputable abbrev QuantumRegWithBasis (R : TypeQuantumRegister) (p : QuantumRegHasBasis R)
  : TypeBasisRegister := ⟨R.space, ⟨p.choose, QuantRegToBasis R p⟩⟩



@[coe]
public noncomputable abbrev QuantumRegCatElement (R : TypeBasisRegister) : ObjectProperty.FullSubcategory QuantumRegHasBasis where
  obj := BasisRegToQuantReg R
  property := ⟨R.indexing, ⟨R.struct.toBasis, R.struct.isOrthonormal⟩⟩

public noncomputable instance : Coe TypeBasisRegister (ObjectProperty.FullSubcategory QuantumRegHasBasis) where
  coe := QuantumRegCatElement

@[coe]
public noncomputable abbrev CatElementQuantumReg (X : ObjectProperty.FullSubcategory QuantumRegHasBasis) : TypeBasisRegister :=
  QuantumRegWithBasis X.obj X.property

public noncomputable instance : Coe (ObjectProperty.FullSubcategory QuantumRegHasBasis) TypeBasisRegister where
  coe := CatElementQuantumReg

/-
    This property is Monoidal (Respects Tensor and holds the unit)
-/

@[default_instance]
public noncomputable instance HavingBasisIsMonoidal : ObjectProperty.IsMonoidal QuantumRegHasBasis where
  prop_unit := ⟨(Fin 1), ⟨CIsHilbertBasis.toBasis, CIsHilbertBasis.isOrthonormal⟩⟩
  prop_tensor X Y hasBasisX hasBasisY :=
  ⟨(hasBasisX.choose × hasBasisY.choose),
  ⟨(HilbertBasisTensorFun X.space Y.space hasBasisX.choose hasBasisY.choose).toBasis,
   (HilbertBasisTensorFun X.space Y.space hasBasisX.choose hasBasisY.choose).isOrthonormal⟩⟩

/-
    The subcategory of Hilbert spaces with basis is a full monoidal subcategory
    of the previously constructed monoidal category
-/


/-

    The right category for TypeBasisRegister __depends__ on the chosen basis,
    Simply quotienting by the proposition "there exists a basis" is not enough, the axiom
    of choice obscures the chosen basis which creates problems when defining isometries
    between basis

    The right construction is as follows (as the dependent product does not exist yet afaik):


    *Hilb* ────────⟩ *Hilb* × Types
                          ∣
                          ∣   Quotient by property : Makes a basis
                          ∣
                          ∨
                    *BasisMonCat*
-/



@[default_instance]
public noncomputable instance CatBasisReg' : Category (ObjectProperty.FullSubcategory QuantumRegHasBasis) :=
  ObjectProperty.FullSubcategory.category QuantumRegHasBasis

@[default_instance]
public noncomputable instance CatBasisReg : Category TypeBasisRegister where
  Hom X Y := CatBasisReg'.Hom (QuantumRegCatElement X) (QuantumRegCatElement Y)
  id X := CatBasisReg'.id (QuantumRegCatElement X)
  comp f g := CatBasisReg'.comp f g

@[default_instance]
public noncomputable instance MonCatBasisReg : MonoidalCategory (ObjectProperty.FullSubcategory QuantumRegHasBasis) :=
  ObjectProperty.fullMonoidalSubcategory QuantumRegHasBasis

notation A "⊗ᵣ" B => MonCatBasisReg.tensorObj A B

public noncomputable def id_map (R : TypeBasisRegister) : R ⟶ R := CatBasisReg.id R

--@[default_instance]
--public noncomputable instance MonCatBasisReg : MonoidalCategory TypeBasisRegister where
--  tensorObj X Y := CatElementQuantumReg (MonCatBasisReg'.tensorObj (QuantumRegCatElement X) (QuantumRegCatElement Y))
--  whiskerLeft X Y Z f := @MonCatBasisReg'.whiskerLeft (QuantumRegCatElement X) (QuantumRegCatElement Y) (QuantumRegCatElement Z) f
--  whiskerRight f Z := MonCatBasisReg'.whiskerRight f (QuantumRegCatElement Z)
--  tensorUnit :=  CatElementQuantumReg (MonCatBasisReg'.tensorUnit)
--  associator X Y Z := MonCatBasisReg'.associator (QuantumRegCatElement X) (QuantumRegCatElement Y) (QuantumRegCatElement Z)
--  leftAssociator := MonCatBasisReg'.leftAssociator
--  rightAssociator := MonCatBasisReg'.rightAssociator

end BasisRegister
