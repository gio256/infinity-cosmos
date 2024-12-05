import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Homotopy
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.StrictSegal
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialObject.Basic

universe u

open SSet StrictSegal Simplicial

namespace CategoryTheory.SSet

open Opposite in
instance (S : SSet.{u}) [StrictSegal S] : Category.{u} (OneTruncation S) where
  id := 𝟙rq
  comp {X Y Z} f g := by
    refine ⟨?_, ?_⟩
    · apply StrictSegal.spineToDiagonal (n := 2)
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
        change S.δ 1 _ = X
        rw [δ_one_spineToDiagonal]
      · unfold OneTruncation.tgt
        change S.δ 0 _ = Z
        rw [δ_zero_spineToDiagonal]
  id_comp {X Y} f := by
    have hrfl := HomotopyR.refl f.val
    apply Subtype.ext
    have : spineToDiagonal (S.spine 2 hrfl.simplex) = f.val := by
      simp only [spineToDiagonal, spineToSimplex_spine]
      rw [← SimplicialObject.δ_one_one]
      exact hrfl.δ₁
    rw [← this]
    apply congr_arg spineToDiagonal
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, spine_arrow]
      rw [← SimplicialObject.δ_one_two, hrfl.δ₂]
      change _ = S.σ _ (OneTruncation.src f.val)
      rw [f.property.left]
      rfl
    · simp only [Fin.mk_one, spine_arrow]
      rw [← SimplicialObject.δ_one_zero]
      exact hrfl.δ₀.symm
  comp_id {X Y} f := by
    have hrfl := HomotopyL.refl f.val
    apply Subtype.ext
    have : spineToDiagonal (S.spine 2 hrfl.simplex) = f.val := by
      simp only [spineToDiagonal, spineToSimplex_spine]
      rw [← SimplicialObject.δ_one_one]
      exact hrfl.δ₁
    rw [← this]
    apply congr_arg spineToDiagonal
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, spine_arrow]
      rw [← SimplicialObject.δ_one_two]
      exact hrfl.δ₂.symm
    · simp only [Fin.mk_one, spine_arrow]
      rw [← SimplicialObject.δ_one_zero, hrfl.δ₀]
      change _ = S.σ _ (OneTruncation.tgt f.val)
      rw [f.property.right]
      rfl
  assoc {W X Y Z} f g h := by
    sorry

end CategoryTheory.SSet
