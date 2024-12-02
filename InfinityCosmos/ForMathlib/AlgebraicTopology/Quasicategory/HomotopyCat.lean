import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.StrictSegal
import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal

universe u

open SSet StrictSegal Simplicial

namespace CategoryTheory.SSet

lemma interval_full (X : SSet.{u}) {n : ℕ} (f : Path X n) :
    f.interval 0 n (by omega) = f := by
  ext i <;> simp [Path.interval]

lemma foo (X : SSet.{u}) [StrictSegal X] (f : Path X 2)
    (h : f.arrow 0 = X.σ 0 (f.vertex 0)) :
    spineToDiagonal f = f.arrow 1 := by
  simp [spineToDiagonal]
  /- apply (SSet.yonedaEquiv X [1]).symm.injective -/
  /- ext n x -/
  have : spineToSimplex f = X.σ 0 (f.arrow 1) := by
    apply spineInjective
    simp [spineEquiv]
    rw [spine_spineToSimplex]
    ext i
    fin_cases i
    · sorry
    · sorry
  sorry

open Opposite in
instance (S : SSet.{u}) [StrictSegal S] : Category.{u} (OneTruncation S) where
  id := 𝟙rq
  comp {X Y Z} f g := by
    refine ⟨?_, ?_⟩
    ·
      /- #check (SSet.yonedaEquiv S [1]).symm f.1 -/
      /- apply SimplicialObject.diagonal (n := 2) S -/
      /- #check S.map (SimplexCategory.mkOfLeComp (n := 2) 0 1 2 _ _).op -/
      /- refine SSet.yonedaEquiv S [2] ?_ -/
      apply StrictSegal.spineToDiagonal (n := 2)
      exact {
        vertex := fun | 0 => X | 1 => Y | 2 => Z
        arrow := fun | 0 => f.val | 1 => g.val
        arrow_src := by
          intro i
          fin_cases i
          · exact f.property.left
          · exact g.property.left
        arrow_tgt := by
          intro i
          fin_cases i
          · exact f.property.right
          · exact g.property.right }
    · apply And.intro
      · unfold OneTruncation.src
        rw [δ_one_spineToDiagonal]
      · unfold OneTruncation.tgt
        rw [δ_zero_spineToDiagonal]
  id_comp {X Y} f := by
    ext
    simp only [Nat.reduceAdd, ReflQuiver.id]
    simp only [spineToDiagonal, SimplicialObject.diagonal]
    /- rw [← interval_full (n := 2) _ { -/
    /-   vertex := fun x ↦ -/
    /-     match x with -/
    /-     | 0 => X -/
    /-     | 1 => X -/
    /-     | 2 => Y -/
    /-   arrow := fun x ↦ -/
    /-     match x with -/
    /-     | 0 => SimplicialObject.σ S 0 X -/
    /-     | 1 => f.val -/
    /-   arrow_src := _ -/
    /-   arrow_tgt := _ }] -/
    /- rw [← spineToSimplex_interval] -/
    /- rw [← FunctorToTypes.map_comp_apply, ← op_comp] -/
    /- simp only [SimplexCategory.diag_subinterval_eq] -/
    /- #check SimplexCategory.mkOfSucc_δ_eq (n := 1) (i := 0) (j := 1) (by omega) -/
    /- #check Fin.val_zero -/
    /- rw [← Fin.val_zero 1] -/
    /- conv => lhs; congr; congr; rw [← SimplexCategory.mkOfSucc_δ_eq (i := 0)] -/
    /- rw [← SimplexCategory.mkOfSucc_δ_eq (i := 0) (j := 1) _] -/

    /- apply spineInjective -/
    /- simp [spineEquiv] -/
    /- ext x -/
    /- fin_cases x -/
    /- simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue] -/
    /- simp -/
    /- rw [← FunctorToTypes.map_comp_apply, ← op_comp] -/
    sorry
  comp_id {X Y} f := by
    sorry
  assoc {W X Y Z} f g h := by
    sorry

end CategoryTheory.SSet
/- id X := by -/
/-   refine ⟨S.σ 0 X, ?_⟩ -/
/-   apply And.intro -/
/-   · simp only [OneTruncation.src] -/
/-     rw [← types_comp_apply (SimplicialObject.σ _ _) (SimplicialObject.δ _ _)] -/
/-     rw [← Fin.succ_zero_eq_one, SimplicialObject.δ_comp_σ_succ] -/
/-     rfl -/
/-   · simp only [OneTruncation.tgt] -/
/-     rw [← types_comp_apply (SimplicialObject.σ _ _) (SimplicialObject.δ _ _)] -/
/-     rw [← Fin.castSucc_zero, SimplicialObject.δ_comp_σ_self] -/
/-     rfl -/
