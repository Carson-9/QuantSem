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

namespace BasisRegister'

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

@[simp]
public theorem BasisRegQuantRegSpace (R : TypeBasisRegister ) :
  R.space = (BasisRegToQuantReg R).space := by rfl

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

--notation A "⊗ᵣ" B => MonCatBasisReg.tensorObj A B

public noncomputable def id_map (R : TypeBasisRegister) : R ⟶ R := CatBasisReg.id R

end BasisRegister'



/-
    Hard instantiation
-/


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

@[default_instance]
public instance CatBasisReg'' : Category TypeBasisRegister where
  Hom X Y := X.space →ₗᵢ[ℂ] Y.space
  id X := LinearIsometry.id
  comp f g := LinearIsometry.comp g f

@[ext]
public theorem CatRegisterHomExt {R1 R2 : TypeBasisRegister} (f g : R1 ⟶ R2) :
  (∀ x : R1.space, f.toFun x = g.toFun x) → f = g :=
  by intro h; apply LinearIsometry.ext_iff.mpr; apply h

public theorem CatRegisterHomExtIff {R1 R2 : TypeBasisRegister} (f g : R1 ⟶ R2) :
  f = g ↔ (∀ x : R1.space, f.toFun x = g.toFun x) :=
  by apply Iff.intro; intro hEq; rw[hEq]; intro x; rfl; apply CatRegisterHomExt


@[expose]
public noncomputable def BasisRegisterTensor (T1 T2 : TypeBasisRegister) : TypeBasisRegister :=
  ⟨TensorProduct ℂ T1.space T2.space, ⟨T1.indexing × T2.indexing, @HilbertBasisTensorFun T1.space T2.space T1.indexing T2.indexing T1.struct T2.struct ⟩⟩

notation A "⊗ᵣ" B => BasisRegisterTensor A B

@[simp]
public theorem SpaceCommutesWithTensor (R1 R2 : TypeBasisRegister) :
  (R1 ⊗ᵣ R2).space = TensorProduct ℂ R1.space R2.space := by rfl


public def StatesAsCombinationOfSeparables {R1 R2 : TypeBasisRegister} :
  (R1 ⊗ᵣ R2).space ≃
    Submodule.span ℂ {t : TensorProduct ℂ R1.space R2.space | ∃ (m : R1.space) (n : R2.space), m ⊗ₜ[ℂ] n = t} :=
    .mk (fun x => ⟨x, by rw[TensorProduct.span_tmul_eq_top ℂ R1.space R2.space]; simp⟩) (fun a => a.val)
    (by unfold Function.LeftInverse; intro x; simp)
    (by unfold Function.RightInverse; intro x; simp)

public theorem RegisterInduction{R1 R2 : TypeBasisRegister}
  (property : (R1 ⊗ᵣ R2).space → Prop)
  (hzero : property 0)
  (hAllBasis : ∀ x1 : R1.space, ∀ x2 : R2.space, property (x1 ⊗ₜ[ℂ] x2))
  (hLinear : ∀ x1 x2 : ((R1 ⊗ᵣ R2).space), property x1 → property x2 → property (x1 + x2))
  (hmul :  ∀ x : ((R1 ⊗ᵣ R2).space), ∀ c : ℂ, property x → property (c • x)) :
  ∀ x : ((R1 ⊗ᵣ R2).space), property x :=
  by intro x; sorry
  -- submodule span induction

@[expose]
public noncomputable def BasisRegHomTensor {R1 R2 R3 R4 : TypeBasisRegister}
  (f : R1 ⟶ R3) (g : R2 ⟶ R4) :
  (R1 ⊗ᵣ R2) ⟶ (R3 ⊗ᵣ R4) :=
  @QuantumTypes.TensorLinearIsometries R1.space R2.space R3.space R4.space
    R1.struct.toHilbertSpace R2.struct.toHilbertSpace R3.struct.toHilbertSpace R4.struct.toHilbertSpace
    (f : R1.fst →ₗᵢ[ℂ] R3.fst) g

--notation f "⊗ₕ" g => BasisRegHomTensor f g


@[simp]
public theorem arrow_is_comp {R1 R2 R3 : TypeBasisRegister} (f : R1 ⟶ R2) (g : R2 ⟶ R3)
  : (f ≫ g) = (LinearIsometry.comp g f) := by rfl

@[expose]
public def id_map (R : TypeBasisRegister) : R ⟶ R := @QuantumTypes.IdMap R.space R.struct.toHilbertSpace

@[simp]
public theorem id_map_is_neutral_left {R1 R2 : TypeBasisRegister}
  (f : R1 ⟶ R2) : id_map R1 ≫ f = f := by rfl

@[simp]
public theorem id_map_is_neutral_right {R1 R2 : TypeBasisRegister}
  (f : R1 ⟶ R2) : f ≫ id_map R2 = f := by rfl

@[simp]
public theorem id_tensor_id : ∀ X Y : TypeBasisRegister,
  BasisRegHomTensor (id_map X) (id_map Y) = id_map (X ⊗ᵣ Y) :=
  by intro X Y; apply @QuantumTypes.TensorOfIdIsId X.space Y.space X.struct.toHilbertSpace Y.struct.toHilbertSpace

@[simp]
public theorem one_is_id : ∀ X : TypeBasisRegister, 𝟙 X = id_map X :=
  by intro X; rfl

@[simp]
public theorem tensor_factorises : ∀ A A' C B B' D, ∀ (f : A' ⟶ C) (g : B' ⟶ D)
  (h : A ⟶ A') (i : B ⟶ B'),
  (BasisRegHomTensor h i) ≫ (BasisRegHomTensor f g) = BasisRegHomTensor (h ≫ f) (i ≫ g) :=
  by intro A A' B B' C D f g h i;
     apply @QuantumTypes.TensorFactorises
      A.space A'.space B.space B'.space C.space D.space
      A.struct.toHilbertSpace A'.struct.toHilbertSpace B.struct.toHilbertSpace B'.struct.toHilbertSpace
      C.struct.toHilbertSpace D.struct.toHilbertSpace f g h i

@[simp]
public theorem id_is_neutral_left : ∀ A B : TypeBasisRegister, ∀ (f : A ⟶ B),
  f ≫ (id_map B) = f :=
    by intro A B f;
       apply (@QuantumTypes.IdIsNeutralLeft A.space B.space A.struct.toHilbertSpace B.struct.toHilbertSpace f)

@[simp]
public theorem id_is_neutral_right : ∀ A B : TypeBasisRegister, ∀ (f : A ⟶ B),
  (id_map A) ≫ f = f :=
    by intro A B f;
       apply (@QuantumTypes.IdIsNeutralRight A.space B.space A.struct.toHilbertSpace B.struct.toHilbertSpace f)


@[expose]
public noncomputable def BasisRegHomTensorAssoc (R1 R2 R3 : TypeBasisRegister) :
  ((R1 ⊗ᵣ R2) ⊗ᵣ R3) ≅ (R1 ⊗ᵣ (R2 ⊗ᵣ R3)) :=
  Iso.mk
    (existingIso.toLinearIsometry)
    (existingIso.symm.toLinearIsometry)
    (by rw[one_is_id]; unfold CategoryStruct.comp; unfold CatBasisReg''; simp; apply (QuantumTypes.EquivalenceToIsometryOfSymmRight existingIso))
    (by rw[one_is_id]; unfold CategoryStruct.comp; unfold CatBasisReg''; simp; apply (QuantumTypes.EquivalenceToIsometryOfSymmLeft existingIso))
    where existingIso := @QuantumTypes.HilbertTensorAssoc R1.space R2.space R3.space R1.struct.toHilbertSpace R2.struct.toHilbertSpace R3.struct.toHilbertSpace


@[expose]
public noncomputable def CLeftUnitor (R : TypeBasisRegister) :
  (⟨ℂ, ⟨Fin 1, CHilbertBasis⟩⟩ ⊗ᵣ R) ≅ R :=
  Iso.mk
    (existingIso.toLinearIsometry)
    (existingIso.symm.toLinearIsometry)
    (by rw[one_is_id]; unfold CategoryStruct.comp; unfold CatBasisReg''; simp; apply (QuantumTypes.EquivalenceToIsometryOfSymmRight existingIso))
    (by rw[one_is_id]; unfold CategoryStruct.comp; unfold CatBasisReg''; simp; apply (QuantumTypes.EquivalenceToIsometryOfSymmLeft existingIso))
    where existingIso := @QuantumTypes.CIsLeftNeutral R.space R.struct.toHilbertSpace

@[expose]
public noncomputable def CRightUnitor (R : TypeBasisRegister) :
  (R ⊗ᵣ ⟨ℂ, ⟨Fin 1, CHilbertBasis⟩⟩) ≅ R :=
  Iso.mk
    (existingIso.toLinearIsometry)
    (existingIso.symm.toLinearIsometry)
    (by rw[one_is_id]; unfold CategoryStruct.comp; unfold CatBasisReg''; simp; apply (QuantumTypes.EquivalenceToIsometryOfSymmRight existingIso))
    (by rw[one_is_id]; unfold CategoryStruct.comp; unfold CatBasisReg''; simp; apply (QuantumTypes.EquivalenceToIsometryOfSymmLeft existingIso))
    where existingIso := @QuantumTypes.CIsRightNeutral R.space R.struct.toHilbertSpace

-- public theorem AssocNaturality {R1 R2 R3 R4 R5 R6 : TypeBasisRegister}
--   (f : R1 ⟶ R4) (g : R2 ⟶ R5) (h : R3 ⟶ R6) :
--   (((f ⊗ₕ g) ⊗ₕ h) ≫ (BasisRegHomTensorAssoc R4 R5 R6).hom) =
--   ((BasisRegHomTensorAssoc R1 R2 R3).hom ≫ ((f ⊗ₕ (g ⊗ₕ h)))) :=
--   by
--     unfold BasisRegHomTensorAssoc BasisRegHomTensorAssoc.existingIso BasisRegisterTensor
--     unfold BasisRegHomTensor
--     simp; sorry


@[default_instance]
public noncomputable instance MonCatBasisReg' : MonoidalCategory TypeBasisRegister where
  tensorObj := BasisRegisterTensor
  whiskerLeft X Y1 Y2 f := BasisRegHomTensor LinearIsometry.id f
  whiskerRight f Y := BasisRegHomTensor f LinearIsometry.id
  tensorUnit := ⟨ℂ, ⟨Fin 1, CHilbertBasis⟩⟩
  associator X Y Z := BasisRegHomTensorAssoc X Y Z
  leftUnitor X := CLeftUnitor X
  rightUnitor X := CRightUnitor X
  id_tensorHom_id := by intro X Y; simp; sorry
  tensorHom_comp_tensorHom := by
    intro X1 X2 Y1 Y2 Z1 Z2 f g h i; sorry; -- rw[tensor_factorises, tensor_factorises, id_map_is_neutral_left, id_is_neutral_left, id_is_neutral_right, id_is_neutral_right, tensor_factorises, tensor_factorises, id_is_neutral_left, id_is_neutral_right];
  whiskerLeft_id := by intro X Y; rw[one_is_id, one_is_id]; unfold id_map QuantumTypes.IdMap; sorry --rw[QuantumTypes.TensorOfIdIsId]
  id_whiskerRight := by intro X Y; sorry -- rw[one_is_id, id_tensor_id]; rfl
  associator_naturality := by intro X1 X2 X3 Y1 Y2 Y3 f1 f2 f3; simp; ext x; sorry --unfold QuantRegHomTensorAssoc; unfold QuantRegHomTensorAssoc.existingIso; simp; sorry--rw[TensorAssocOverComp]
  leftUnitor_naturality := by intro X Y f; unfold CLeftUnitor; simp; sorry
  rightUnitor_naturality := by intro X Y f; ext x; simp; sorry
  triangle := by intro X Y; ext x; simp; sorry
  pentagon := by sorry

end BasisRegister
