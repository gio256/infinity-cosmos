import Mathlib.AlgebraicTopology.SimplicialSet.Basic

universe v u

namespace SSet

open CategoryTheory Simplicial SimplexCategory Limits

open Fintype in
lemma not_surjective_of_card_lt {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (h : card α < card β) : ¬Function.Surjective f :=
  fun hs ↦ Nat.lt_le_asymm h <| card_le_of_surjective f hs

lemma δ_not_surjective {n : ℕ} (i : Fin (n + 2)) :
    ¬Function.Surjective (δ i).toOrderHom :=
  not_surjective_of_card_lt _ (by simp)

noncomputable def skipped {n : ℕ} {a : SimplexCategoryᵒᵖ} (α : ∂Δ[n].obj a) :
    Fin (n + 1) := Classical.choose <| not_forall.mp α.property

def diagram (n : ℕ) : MultispanIndex SSet where
  L := { (i, j) : Fin (n + 2) × Fin (n + 3) | i.castSucc < j }
  R := Fin (n + 3)
  fstFrom p := p.1.1
  sndFrom p := p.1.2
  left _ := Δ[n]
  right _ := Δ[n + 1]
  fst p := standardSimplex.map <| δ <| p.1.2.pred <| Fin.ne_zero_of_lt p.2
  snd p := standardSimplex.map <| δ p.1.1

abbrev cocone (n : ℕ) : Multicofork (diagram n) := by
  refine Multicofork.ofπ (diagram n) ∂Δ[n + 2] ?_ ?_
  · intro k
    refine {
      app := fun m α ↦ ⟨standardSimplex.map (δ k) |>.app m α, ?_⟩
      naturality := fun a b f ↦ rfl }
    intro h
    /- exact δ_not_surjective k <| Function.Surjective.of_comp h -/
    exact not_surjective_of_card_lt (δ k).toOrderHom (by simp) <|
      Function.Surjective.of_comp h
  · intro ⟨⟨i, j⟩, h⟩
    simp [diagram, MultispanIndex.multispan]
    ext a α
    rw [NatTrans.comp_app, NatTrans.comp_app]
    apply Subtype.ext
    simp only [types_comp_apply]
    rw [← types_comp_apply ((standardSimplex.map _).app _) ((standardSimplex.map _).app _)]
    rw [← NatTrans.comp_app]
    rw [← Functor.map_comp]
    rw [← δ_comp_δ' h]
    rfl

noncomputable def colim (n : ℕ) : IsColimit (cocone n) := by
  refine Multicofork.IsColimit.mk (cocone n) ?_ ?_ ?_
  · intro X
    refine { app := ?_, naturality := ?_ }
    · intro a α
      apply X.π (skipped α) |>.app a
      refine standardSimplex.objEquiv _ _ |>.symm ?_
      exact factor_δ (m := a.unop.len) (standardSimplex.objEquiv _ _ α.1) (skipped α)
    · intro a b f
      ext α
      simp [diagram, MultispanIndex.multispan]
      sorry
  · intro X k
    simp [diagram, MultispanIndex.multispan, Multicofork.π]
    ext a α
    rw [NatTrans.comp_app]
    simp
    sorry
  · intro X
    simp [diagram, MultispanIndex.multispan]
    intro f h
    ext a α
    simp
    sorry

/- noncomputable def colim' (n : ℕ) : ∂Δ[n + 2] ≅ multicoequalizer (diagram n) where -/
end SSet
