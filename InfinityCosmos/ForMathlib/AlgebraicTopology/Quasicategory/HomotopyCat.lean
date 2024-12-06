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
    use StrictSegal.spineToDiagonal (n := 2) {
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
        · exact g.property.right
    }
    apply And.intro
    · unfold OneTruncation.src
      change S.δ 1 _ = X
      rw [δ_one_spineToDiagonal]
    · unfold OneTruncation.tgt
      change S.δ 0 _ = Z
      rw [δ_zero_spineToDiagonal]
  id_comp {X Y} f := by
    have hrfl := HomotopyR.refl f.val
    apply Subtype.ext
    rw [← hrfl.δ₁, SimplicialObject.δ_one_one,
      ← spineToSimplex_spine hrfl.simplex]
    apply congr_arg spineToDiagonal
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, spine_arrow]
      simp only [ReflQuiver.id]
      rw [← SimplicialObject.δ_one_two, hrfl.δ₂]
      apply congr_arg (S.σ 0)
      exact f.property.left.symm
    · simp only [Fin.mk_one, spine_arrow]
      rw [← SimplicialObject.δ_one_zero]
      exact hrfl.δ₀.symm
  comp_id {X Y} f := by
    have hrfl := HomotopyL.refl f.val
    apply Subtype.ext
    rw [← hrfl.δ₁, SimplicialObject.δ_one_one,
      ← spineToSimplex_spine hrfl.simplex]
    apply congr_arg spineToDiagonal
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, spine_arrow]
      rw [← SimplicialObject.δ_one_two]
      exact hrfl.δ₂.symm
    · simp only [Fin.mk_one, spine_arrow]
      simp only [ReflQuiver.id]
      rw [← SimplicialObject.δ_one_zero, hrfl.δ₀]
      apply congr_arg (S.σ 0)
      exact f.property.right.symm
  assoc {W X Y Z} f g h := by
    apply Subtype.ext
    let p : Path S 3 := {
      vertex := fun | 0 => W | 1 => X | 2 => Y | 3 => Z
      arrow := fun | 0 => f.val | 1 => g.val | 2 => h.val
      arrow_src := by
        intro i
        fin_cases i
        · exact f.property.left
        · exact g.property.left
        · exact h.property.left
      arrow_tgt := by
        intro i
        fin_cases i
        · exact f.property.right
        · exact g.property.right
        · exact h.property.right
    }
    trans spineToDiagonal p
    · rw [assoc_left p]
      simp
      apply congr_arg spineToDiagonal
      ext i
      fin_cases i
      · apply congr_arg spineToDiagonal
        ext j
        fin_cases j <;> rfl
      · rfl
    · rw [assoc_right p]
      apply congr_arg spineToDiagonal
      ext i
      fin_cases i
      · rfl
      · apply congr_arg spineToDiagonal
        ext j
        fin_cases j <;> rfl

end CategoryTheory.SSet
