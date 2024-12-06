import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplexCategory
import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal

universe u

open CategoryTheory
open Simplicial SimplicialObject SimplexCategory

namespace SSet.StrictSegal
variable {X : SSet.{u}} [StrictSegal X] {n : ℕ}

lemma δ_one_spineToDiagonal (f : Path X n) :
    X.δ 1 (spineToDiagonal f) = f.vertex 0 := by
  simp only [spineToDiagonal, diagonal, SimplicialObject.δ]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  have : δ 1 ≫ diag n = const [0] [n] 0 := by ext i; fin_cases i; rfl
  rw [this]
  rw [spineToSimplex_vertex]

lemma δ_zero_spineToDiagonal (f : Path X n) :
    X.δ 0 (spineToDiagonal f) = f.vertex n := by
  simp only [spineToDiagonal, diagonal, SimplicialObject.δ]
  rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  have : δ 0 ≫ diag n = const [0] [n] n := by ext i; fin_cases i; rfl
  rw [this]
  rw [spineToSimplex_vertex]

lemma assoc_left (f : Path X 3) : spineToDiagonal f =
    spineToDiagonal (n := 2) {
      vertex := fun | 0 => f.vertex 0 | 1 => f.vertex 2 | 2 => f.vertex 3
      arrow := fun | 0 => spineToDiagonal (f.interval 0 2 (by omega)) | 1 => f.arrow 2
      arrow_src := by
        intro i
        fin_cases i
        · exact δ_one_spineToDiagonal <| f.interval ..
        · exact f.arrow_src 2
      arrow_tgt := by
        intro i
        fin_cases i
        · exact δ_zero_spineToDiagonal <| f.interval ..
        · exact f.arrow_tgt 2
    } := by
  simp [spineToDiagonal, diagonal]
  rw [← diag_two_mkOfLeComp 2 (by omega)]
  simp
  apply congr_arg
  apply spineInjective
  simp [spineEquiv]
  rw [spine_spineToSimplex]
  ext i
  fin_cases i
  · simp
    change _ = spineToDiagonal _
    rw [← spineToSimplex_edge]
    rw [← FunctorToTypes.map_comp_apply, ← op_comp]
    have : mkOfSucc 0 ≫ mkOfLeComp 0 2 3 (by simp) (by aesop) =
        intervalEdge (n := 3) 0 2 (by simp) := by
      ext i
      fin_cases i <;> rfl
    rw [this]
  · simp
    rw [← FunctorToTypes.map_comp_apply, ← op_comp]
    have : mkOfSucc 1 ≫ mkOfLeComp 0 2 3 (by simp) (by aesop) = mkOfSucc (n := 3) 2 := by
      ext i
      fin_cases i <;> rfl
    rw [this]
    rw [← spine_arrow, spine_spineToSimplex]

lemma assoc_right (f : Path X 3) : spineToDiagonal f =
    spineToDiagonal (n := 2) {
      vertex := fun | 0 => f.vertex 0 | 1 => f.vertex 1 | 2 => f.vertex 3
      arrow := fun | 0 => f.arrow 0 | 1 => spineToDiagonal (f.interval 1 2 (by omega))
      arrow_src := by
        intro i
        fin_cases i
        · exact f.arrow_src 0
        · exact δ_one_spineToDiagonal <| f.interval ..
      arrow_tgt := by
        intro i
        fin_cases i
        · exact f.arrow_tgt 0
        · exact δ_zero_spineToDiagonal <| f.interval ..
    } := by
  simp [spineToDiagonal, diagonal]
  rw [← diag_two_mkOfLeComp 1 (by omega)]
  simp
  apply congr_arg
  apply spineInjective
  simp [spineEquiv]
  rw [spine_spineToSimplex]
  ext i
  fin_cases i
  · simp
    rw [← FunctorToTypes.map_comp_apply, ← op_comp]
    have : mkOfSucc 0 ≫ mkOfLeComp 0 1 3 (by simp) (by aesop) = mkOfSucc (n := 3) 0 := by
      ext i
      fin_cases i <;> rfl
    rw [this]
    rw [← spine_arrow, spine_spineToSimplex]
  · simp
    change _ = spineToDiagonal _
    rw [← spineToSimplex_edge]
    rw [← FunctorToTypes.map_comp_apply, ← op_comp]
    have : mkOfSucc 1 ≫ mkOfLeComp 0 1 3 (by simp) (by aesop) =
        intervalEdge (n := 3) 1 2 (by simp) := by
      ext i
      fin_cases i <;> rfl
    rw [this]

end SSet.StrictSegal
