/-
Copyright (c) 2024 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johns Hopkins Category Theory Seminar
-/

import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.CoherentIso
import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal

universe u v w

namespace SSet

open CategoryTheory Simplicial SimplicialCategory

/-- An interval is a simplicial set equipped with two endpoints.-/
class Interval (I : SSet.{u}) : Type u where
  src : Δ[0] ⟶ I
  tgt : Δ[0] ⟶ I

/-- The interval relevant to the theory of Kan complexes.-/
instance arrowInterval : Interval Δ[1] where
  src := standardSimplex.map (SimplexCategory.δ (n := 0) (1))
  tgt := standardSimplex.map (SimplexCategory.δ (n := 0) (0))

/-- The interval relevant to the theory of quasi-categories. -/
instance isoInterval : Interval coherentIso where
  src :=   (yonedaEquiv coherentIso [0]).symm (WalkingIso.coev WalkingIso.zero)
  tgt :=   (yonedaEquiv coherentIso [0]).symm (WalkingIso.coev WalkingIso.one)


open MonoidalCategory
def pointIsUnit : Δ[0] ≅ (𝟙_ SSet) := by sorry

noncomputable def expUnitNatIso : ihom (𝟙_ SSet) ≅ 𝟭 SSet :=
  (conjugateIsoEquiv (Adjunction.id (C := SSet)) (ihom.adjunction _)
    (leftUnitorNatIso _)).symm

def expPointNatIso : ihom Δ[0] ≅ 𝟭 SSet := by sorry
--   refine ?_ ≪≫ expUnitNatIso
--   have := pointIsUnit.symm.op
--   sorry

/-- Once we've proven that `Δ[0]` is terminal, this will follow from something just PRed to mathlib.-/
def expPointIsoSelf (X : SSet) : sHom Δ[0] X ≅ X := sorry

section

variable {I : SSet.{u}} [Interval I]

noncomputable def pathSpace {I : SSet.{u}} [Interval I] (X : SSet.{u}) : SSet.{u} := sHom I X

open MonoidalClosed

noncomputable def pathSpace.src (X : SSet.{u}) : pathSpace (I := I) X ⟶ X :=
  ((MonoidalClosed.pre Interval.src).app X ≫ X.expPointIsoSelf.hom)

noncomputable def pathSpace.tgt (X : SSet.{u}) : pathSpace (I := I) X ⟶ X :=
  ((MonoidalClosed.pre Interval.tgt).app X ≫ X.expPointIsoSelf.hom)


/-- TODO: Figure out how to allow `I` to be an a different universe from `A` and `B`?-/
structure Homotopy {A B : SSet.{u}} (f g : A ⟶ B) : Type u
    where
  homotopy : A ⟶ sHom I B
  source_eq : homotopy ≫ pathSpace.src B = f
  target_eq : homotopy ≫ pathSpace.tgt B = g

/-- For the correct interval, this defines a good notion of equivalences for both Kan complexes
and quasi-categories.-/
structure Equiv (A B : SSet.{u}) : Type u where
  toFun : A ⟶ B
  invFun : B ⟶ A
  left_inv : Homotopy (I := I) (toFun ≫ invFun) (𝟙 A)
  right_inv : Homotopy (I := I) (invFun ≫ toFun) (𝟙 B)

end

section

open SimplexCategory

variable {A : SSet.{u}} (f g : Δ[1] ⟶ A)

structure HomotopyL where
  homotopy : Δ[2] ⟶ A
  face0 : standardSimplex.map (δ 0) ≫ homotopy =
    standardSimplex.map (σ 0) ≫ standardSimplex.map (δ 0) ≫ f
  face1 : standardSimplex.map (δ 1) ≫ homotopy = g
  face2 : standardSimplex.map (δ 2) ≫ homotopy = f

structure HomotopyR where
  homotopy : Δ[2] ⟶ A
  face0 : standardSimplex.map (δ 0) ≫ homotopy = f
  face1 : standardSimplex.map (δ 1) ≫ homotopy = g
  face2 : standardSimplex.map (δ 2) ≫ homotopy =
    standardSimplex.map (σ 0) ≫ standardSimplex.map (δ 1) ≫ f

def HomotopicL : Prop :=
    Nonempty (HomotopyL f g)

def HomotopicR : Prop :=
    Nonempty (HomotopyR f g)

structure HtpyL (f g : A _[1]) where
  simplex : A _[2]
  δ₂ : A.δ 2 simplex = f
  δ₁ : A.δ 1 simplex = g
  δ₀ : A.δ 0 simplex = A.σ 0 (A.δ 0 f)

structure HtpyR (f g : A _[1]) where
  simplex : A _[2]
  δ₂ : A.δ 2 simplex = A.σ 0 (A.δ 1 f)
  δ₁ : A.δ 1 simplex = g
  δ₀ : A.δ 0 simplex = f

def Homotopic (f g : A _[1]) : Prop := Nonempty (HtpyL f g)

def HomotopyR.refl : HomotopyR f f where
  homotopy := standardSimplex.map (σ 0) ≫ f
  face0 := by
    rw [← Category.assoc, ← Functor.map_comp, δ_comp_σ_self' (by simp)]
    simp
  face1 := by
    rw [← Category.assoc, ← Functor.map_comp, δ_comp_σ_succ' (by simp)]
    simp
  face2 := by
    rw [← Category.assoc, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp,
        ← δ_comp_σ_of_gt (by simp)]
    rfl

lemma foo {A : SSet.{u}} (s : A _[2]) : (A.spine 2 s).arrow 0 = A.δ 2 s := by
  have h : mkOfSucc 0 = δ 2 := by
    ext i
    fin_cases i <;> rfl
  simp [SimplicialObject.δ]
  rw [h]

lemma bar {A : SSet.{u}} (s : A _[2]) : (A.spine 2 s).arrow 1 = A.δ 0 s := by
  have h : mkOfSucc 1 = δ 0 := by
    ext i
    fin_cases i <;> rfl
  simp [SimplicialObject.δ]
  rw [h]

lemma baz {A : SSet.{u}} (s : A _[2]) : A.diagonal s = A.δ 1 s := by
  have h : diag 2 = δ 1 := by
    ext i
    fin_cases i <;> rfl
  simp [SimplicialObject.diagonal, SimplicialObject.δ]
  rw [h]

open StrictSegal in
lemma segal_homotopy' [StrictSegal A] (f g : A _[1]) : Homotopic f g ↔ f = g := by
  have hff : HtpyL f f := sorry
  apply Iff.intro <;> intro h
  · have hfg := Classical.choice h
    have hdg : spineToDiagonal (A.spine 2 hfg.simplex) = g := by
      simp [spineToDiagonal]
      rw [spineToSimplex_spine]
      rw [baz]
      exact hfg.δ₁
    have hdf : spineToDiagonal (A.spine 2 hff.simplex) = f := by
      simp [spineToDiagonal]
      rw [spineToSimplex_spine]
      rw [baz]
      exact hff.δ₁
    have hs : A.spine 2 hfg.simplex = A.spine 2 hff.simplex := by
      ext i
      fin_cases i
      · simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue]
        simp only [foo]
        rw [hff.δ₂]
        exact hfg.δ₂
      · simp only [Nat.reduceAdd, Fin.mk_one, Fin.isValue]
        simp only [bar]
        rw [hff.δ₀]
        exact hfg.δ₀
    have hdf : spineToDiagonal (A.spine 2 hfg.simplex) = f := by
      rw [hs]
      exact hdf
    rw [← hdg]
    exact hdf.symm
  · apply Nonempty.intro
    rw [← h]
    exact hff

/- set_option pp.notation false -/
open StrictSegal in
lemma segal_homotopy [StrictSegal A] : HomotopicR f g ↔ f = g := by
  apply Iff.intro <;> intro h
  · have h : HomotopyR f g := Classical.choice h
    apply (SSet.yonedaEquiv _ _).injective
    apply spineInjective
    simp [spineEquiv]
    rw [← Category.id_comp f]
    rw [← h.face0]
    /- #check spine A 2 (yonedaEquiv _ _ h.homotopy) -/
    have hd : diag 2 = δ 1 := by
      ext i
      fin_cases i <;> rfl
    have ha : SimplicialObject.diagonal A (yonedaEquiv _ _ h.homotopy) = yonedaEquiv _ _ g := by
      simp [SimplicialObject.diagonal]
      rw [hd]
      conv => rhs; rw [← h.face1]
      simp
      /- rw [← types_comp_apply (A.yonedaEquiv [2]) (A.map _)] -/
      /- simp [yonedaEquiv, yonedaCompUliftFunctorEquiv] -/
      /- rw [← types_comp_apply (h.homotopy.app _) (A.map _)] -/

      sorry
    have hh : spineToDiagonal (spine A 2 (yonedaEquiv _ _ h.homotopy)) = yonedaEquiv _ _ g := by
      simp [spineToDiagonal]
      simp [spineToSimplex_spine]
      simp [SimplicialObject.diagonal]

      sorry
    ext i
    fin_cases i
    simp
    sorry
    /- ext n x -/
    /- apply (SSet.yonedaEquiv _ _).injective -/
  · apply Nonempty.intro
    rw [← h]
    exact HomotopyR.refl f

lemma HomotopyR.equiv : --[Quasicategory A] :
    Equivalence (fun f g : Δ[1] ⟶ A ↦ HomotopicR f g) where
  refl f := ⟨HomotopyR.refl f⟩
  symm := sorry
  trans := sorry

lemma homotopicL_iff_homotopicR : --[Quasicategory A]
    HomotopicL f g ↔ HomotopicR f g := sorry

lemma HomotopyL.equiv : --[Quasicategory A]
    Equivalence (fun f g : Δ[1] ⟶ A ↦ HomotopicL f g) := by
  simp [homotopicL_iff_homotopicR]
  exact HomotopyR.equiv

end

end SSet
