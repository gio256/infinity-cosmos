import Mathlib.AlgebraicTopology.SimplicialSet.Basic

universe v u

namespace SSet

open CategoryTheory Simplicial SimplexCategory Limits

open Fintype in
lemma not_surjective_of_card_lt {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (h : card α < card β) : ¬Function.Surjective f :=
  Nat.lt_le_asymm h ∘ card_le_of_surjective f

lemma δ_not_surjective {n : ℕ} (i : Fin (n + 2)) :
    ¬Function.Surjective (δ i).toOrderHom :=
  not_surjective_of_card_lt _ (by simp)

/-- Any `j` not in the image of `δ i` must be equal to `i`. -/
lemma δ_skips_eq {n : ℕ} (i j : Fin (n + 2)) (h : ¬∃ a, (δ i).toOrderHom a = j) :
    j = i := by simp_all [δ]

noncomputable def skipped {n : ℕ} {a : SimplexCategoryᵒᵖ} (α : ∂Δ[n].obj a) :
    Fin (n + 1) := Classical.choose <| not_forall.mp α.property

def beta {n : ℕ} {m : SimplexCategoryᵒᵖ} (α : Δ[n + 1].obj m)
    (i : Fin (n + 2)) : Δ[n].obj m :=
  standardSimplex.map (σ (Fin.predAbove 0 i)) |>.app m α
  /- objEquiv [n] m |>.symm <| factor_δ (m := m.unop.len) (objEquiv [n + 1] m α) i -/

section PredAbove
open Fin

variable {n : ℕ}

lemma predAbove_eq_lt_iff {p j : Fin n} (i : Fin (n + 1)) (h : j < p) :
    p.predAbove i = j ↔ i = j.castSucc := by
  by_cases hi : p.castSucc < i
  · apply Iff.intro <;> rintro rfl
    · rw [predAbove_of_castSucc_lt _ _ hi] at h
      exact False.elim <| not_lt.mpr ((le_pred_iff _).mpr hi) h
    · exact False.elim <| not_le.mpr hi (le_of_lt h)
  · rw [predAbove_of_le_castSucc _ _ (not_lt.mp hi)]
    apply castPred_eq_iff_eq_castSucc

lemma predAbove_eq_iff (p : Fin n) (i : Fin (n + 1)) :
    p.predAbove i = p ↔ i = p.castSucc ∨ i = p.succ := by
  apply Iff.intro
  · intro hp
    by_cases hi : p.castSucc < i
    · rw [predAbove_of_castSucc_lt _ _ hi] at hp
      simp only [← hp, succ_pred, or_true]
    · rw [predAbove_of_le_castSucc _ _ (not_lt.mp hi)] at hp
      simp only [← hp, castSucc_castPred, true_or]
  · rintro (rfl | rfl)
    · rw [predAbove_castSucc_self]
    · rw [predAbove_succ_self]

lemma predAbove_eq_gt_iff {p j : Fin n} (i : Fin (n + 1)) (h : p < j) :
    p.predAbove i = j ↔ i = j.succ := by
  by_cases hi : p.castSucc < i
  . rw [predAbove_of_castSucc_lt _ _ hi]
    apply pred_eq_iff_eq_succ
  · apply Iff.intro <;> rintro rfl
    · rw [predAbove_of_le_castSucc _ _ (not_lt.mp hi)] at h
      exact False.elim <| hi <| (lt_castPred_iff _).mp h
    · exact False.elim <| lt_asymm h <| succ_le_castSucc_iff.mp <| not_lt.mp hi

end PredAbove

lemma σ_eq_lt_iff {n : ℕ} (i k : Fin (n + 1)) (h :  k < i)
    (j : Fin (n + 2)) : (σ i).toOrderHom j = k ↔ j = k.castSucc :=
  predAbove_eq_lt_iff j h

lemma σ_eq_iff {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) :
    (σ i).toOrderHom j = i ↔ j = i.castSucc ∨ j = i.succ :=
  predAbove_eq_iff i j

lemma σ_eq_gt_iff {n : ℕ} (i k : Fin (n + 1)) (h : i < k) (j : Fin (n + 2)) :
    (σ i).toOrderHom j = k ↔ j = k.succ :=
  predAbove_eq_gt_iff j h

def diagram (n : ℕ) : MultispanIndex SSet where
  L := { (i, j) : Fin (n + 2) × Fin (n + 3) | i.castSucc < j }
  R := Fin (n + 3)
  fstFrom p := p.1.1.castSucc
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

open Fin standardSimplex Opposite in
lemma beta_pi {n : ℕ} (X : Multicofork (diagram n))
    {m : SimplexCategoryᵒᵖ} (α : Δ[n + 2].obj m)
    (i : Fin (n + 3))  (hi : ∀ x, (asOrderHom α) x ≠ i)
    (j : Fin (n + 3))  (hj : ∀ x, (asOrderHom α) x ≠ j) :
    (X.π i).app m (beta α i) = (X.π j).app m (beta α j) := by
  obtain rfl | hij | hji : i = j ∨ i < j ∨ j < i := by omega
  · rfl
  · let i' : Fin (n + 2) := i.castPred <| Fin.ne_last_of_lt hij
    have hi' : i = i'.castSucc := by aesop
    let ij : { (i, j) : Fin (n + 2) × Fin (n + 3) | i.castSucc < j } :=
      ⟨(i', j), hij⟩
    let γ := beta (beta α j) i'
    have hu : ((diagram n).snd ij).app m γ = beta α j := by
      simp [diagram, γ, beta]
      simp [standardSimplex, uliftFunctor]
      rw [Fin.predAbove_zero_of_ne_zero (Fin.ne_zero_of_lt hij)]
      change factor_δ (m := m.unop.len) (_ ≫ σ _) i' ≫ δ i' = _
      rw [factor_δ_spec]
      intro k
      simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
      let jp := j.pred (Fin.ne_zero_of_lt hij)
      have hh : i' ≤ jp :=
        (castPred_le_pred_iff (ne_last_of_lt hij) (Fin.ne_zero_of_lt hij)).mpr hij
      obtain hh | hh : i' < jp ∨ i' = jp := Fin.lt_or_eq_of_le hh
      · simp
        have := σ_eq_lt_iff jp i' hh (asOrderHom α k)
        simp [asOrderHom] at this
        rw [this]
        exact hi k
      · simp
        simp [jp] at hh
        rw [← hh]
        have := σ_eq_iff i' (asOrderHom α k)
        simp [asOrderHom] at this
        rw [this]
        intro hn
        rcases hn with hn | hn
        · exact hi k hn
        · rw [hh] at hn
          simp at hn
          exact hj k hn

    have hv : ((diagram n).fst ij).app m γ = beta α i := by
      simp [diagram, γ, beta]
      simp [standardSimplex, uliftFunctor]
      rw [Fin.predAbove_zero_of_ne_zero (Fin.ne_zero_of_lt hij)]
      sorry

    rw [← hu, ← hv]
    rw [← types_comp_apply _ ((X.π _).app m), ← types_comp_apply _ ((X.π _).app m)]
    rw [← NatTrans.comp_app, ← NatTrans.comp_app]
    erw [← X.condition ij]
    rfl
  · sorry

/- set_option pp.proofs true -/
open Opposite standardSimplex in
noncomputable def colim (n : ℕ) : IsColimit (cocone n) := by
  refine Multicofork.IsColimit.mk (cocone n) ?_ ?_ ?_
  · intro X
    refine { app := ?_, naturality := ?_ }
    · intro m α
      exact X.π (skipped α) |>.app m <| beta α.1 (skipped α)
    · intro a b f
      ext α
      simp [diagram, MultispanIndex.multispan, boundary]
      rw [← types_comp_apply ((X.π _).app a) (X.pt.map f)]
      rw [← (X.π _).naturality]
      rw [beta_pi X (Δ[n + 2].map f α.1) _ _ (skipped α)]
      · rfl
      · intro x
        have h := Classical.choose_spec <| not_forall.mp <| α.2
        simp only [skipped, not_exists] at h ⊢
        apply h
      · intro x
        have h := Classical.choose_spec <| not_forall.mp <| boundary.proof_1 (n + 2) f α
        simp only [skipped, not_exists] at h ⊢
        apply h
  · intro X k
    simp [diagram, MultispanIndex.multispan, Multicofork.π] at k ⊢
    ext m α
    rw [NatTrans.comp_app]
    simp only [types_comp_apply]
    rw [Multicofork.π_eq_app_right, Multicofork.π_eq_app_right]
    rw [beta_pi X ((standardSimplex.map (δ k)).app m α) _ _ k]
    · simp [beta, standardSimplex, uliftFunctor]
      cases' k using Fin.cases with k
      · rw [Fin.predAbove_right_zero, δ_comp_σ_self' (by rfl), Category.comp_id]
        rfl
      · rw [Fin.predAbove_zero_succ, δ_comp_σ_succ, Category.comp_id]
        rfl
    · intro x
      exact Fin.succAbove_ne k _
    · have h := Classical.choose_spec <| not_forall.mp <| cocone.proof_1 n k m α
      simp only [skipped, not_exists] at h ⊢
      exact h
  · intro X
    simp [diagram, MultispanIndex.multispan]
    intro f h
    ext m α
    simp
    rw [← h (skipped α)]
    rw [NatTrans.comp_app]
    apply congr_arg
    simp [cocone, Multicofork.π, beta, boundary]
    ext
    simp only
    rw [← types_comp_apply ((standardSimplex.map _).app m) ((standardSimplex.map _).app m)]
    rw [← NatTrans.comp_app]
    rw [← Functor.map_comp]
    simp [standardSimplex, uliftFunctor]
    have hs := Classical.choose_spec <| not_forall.mp <| α.2
    simp [← ne_eq] at hs
    simp [skipped]
    erw [factor_δ_spec _ _ hs]
    rfl

end SSet
