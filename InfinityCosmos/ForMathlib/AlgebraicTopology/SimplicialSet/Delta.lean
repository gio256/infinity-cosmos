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

noncomputable def skipped {n : ℕ} {a : SimplexCategoryᵒᵖ} (α : ∂Δ[n].obj a) :
    Fin (n + 1) := Classical.choose <| not_forall.mp α.property

section PredAbove
open Fin
variable {n : ℕ}

lemma predAbove_eq_lt_iff {p j : Fin n} (h : j < p) (i : Fin (n + 1)) :
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

lemma predAbove_eq_gt_iff {p j : Fin n} (h : p < j) (i : Fin (n + 1)) :
    p.predAbove i = j ↔ i = j.succ := by
  by_cases hi : p.castSucc < i
  . rw [predAbove_of_castSucc_lt _ _ hi]
    apply pred_eq_iff_eq_succ
  · apply Iff.intro <;> rintro rfl
    · rw [predAbove_of_le_castSucc _ _ (not_lt.mp hi)] at h
      exact False.elim <| hi <| (lt_castPred_iff _).mp h
    · exact False.elim <| lt_asymm h <| succ_le_castSucc_iff.mp <| not_lt.mp hi

/- lemma pred_lt_foo (p : Fin n) (i : Fin (n + 1)) (h : i ≠ 0) : -/
/-     castSucc p < i ∨ i.pred h < p := by -/
/-   sorry -/

lemma predAbove_lt_iff_lt_castSucc (p : Fin n) (i : Fin (n + 1)) :
    p.predAbove i < p ↔ i < p.castSucc := by
  apply Iff.intro
  · intro h
    by_cases hi : p.castSucc < i
    · rw [predAbove_of_castSucc_lt _ _ hi] at h
      exact False.elim <| not_lt.mpr ((le_pred_iff _).mpr hi) h
    · rw [predAbove_of_le_castSucc _ _ (not_lt.mp hi)] at h
      exact h
  · intro h
    rw [predAbove_of_le_castSucc _ _ (le_of_lt h)]
    exact h

lemma lt_predAbove_iff_succ_lt (p : Fin n) (i : Fin (n + 1)) :
    p < p.predAbove i ↔ p.succ < i := by
  apply Iff.intro
  · intro h
    by_cases hi : p.castSucc < i
    · rw [predAbove_of_castSucc_lt _ _ hi] at h
      exact lt_pred_iff (ne_zero_of_lt hi) |>.mp h
    · rw [predAbove_of_le_castSucc _ _ (not_lt.mp hi)] at h
      exact False.elim <| hi h
  · intro h
    rw [predAbove_of_succ_le _ _ (le_of_lt h)]
    exact lt_pred_iff (ne_zero_of_lt h) |>.mpr h

/- lemma predAbove_lt_iff_le_succ (p : Fin n) (i : Fin (n + 1)) : -/
/-     p.predAbove i < p ↔ i ≤ p.succ := by -/
/-   rw [predAbove_lt_iff_lt_castSucc] -/

end PredAbove

section SuccAbove
open Fin
variable {n : ℕ} {p : Fin (n + 1)}

lemma succAbove_eq_lt_iff {j : Fin (n + 1)} (h : j < p) (i : Fin n) :
    p.succAbove i = j ↔ i.castSucc = j := by
  by_cases hi : i.castSucc < p
  · rw [succAbove_of_castSucc_lt _ _ hi]
  · apply Iff.intro <;> rintro rfl
    · rw [succAbove_of_le_castSucc _ _ (not_lt.mp hi)] at h
      exact False.elim <| hi <| lt_succ |>.trans h
    · exact False.elim <| hi h

lemma succAbove_eq_gt_iff {j : Fin (n + 1)} (h : p < j) (i : Fin n) :
    p.succAbove i = j ↔ i.succ = j := by
  by_cases hi : i.castSucc < p
  · apply Iff.intro <;> rintro rfl
    · rw [succAbove_of_castSucc_lt _ _ hi] at h
      exact False.elim <| lt_asymm hi h
    · exact False.elim <| (not_lt.mpr (castSucc_lt_iff_succ_le.mp hi)) h
  · rw [succAbove_of_le_castSucc _ _ (not_lt.mp hi)]

end SuccAbove

lemma σ_eq_lt_iff {n : ℕ} {i k : Fin (n + 1)} (h :  k < i)
    (j : Fin (n + 2)) : (σ i).toOrderHom j = k ↔ j = k.castSucc :=
  predAbove_eq_lt_iff h j

lemma σ_eq_iff {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) :
    (σ i).toOrderHom j = i ↔ j = i.castSucc ∨ j = i.succ :=
  predAbove_eq_iff i j

lemma σ_eq_gt_iff {n : ℕ} {i k : Fin (n + 1)} (h : i < k) (j : Fin (n + 2)) :
    (σ i).toOrderHom j = k ↔ j = k.succ :=
  predAbove_eq_gt_iff h j

lemma δ_eq_lt_iff {n : ℕ} {i k : Fin (n + 2)} (h : k < i)
    (j : Fin (n + 1)) : (δ i).toOrderHom j = k ↔ j.castSucc = k :=
  succAbove_eq_lt_iff h j

lemma δ_neq {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (δ i).toOrderHom j ≠ i := Fin.succAbove_ne i j

lemma δ_eq_gt_iff {n : ℕ} {i k : Fin (n + 2)} (h : i < k)
    (j : Fin (n + 1)) : (δ i).toOrderHom j = k ↔ j.succ = k :=
  succAbove_eq_gt_iff h j

def beta {n : ℕ} {m : SimplexCategoryᵒᵖ} (α : Δ[n + 1].obj m)
    (i : Fin (n + 2)) : Δ[n].obj m :=
  standardSimplex.map (σ (Fin.predAbove 0 i)) |>.app m α

def gamma {n : ℕ} {m : SimplexCategoryᵒᵖ} (α : Δ[n + 2].obj m)
    (i : Fin (n + 2)) (j : Fin (n + 3)) : Δ[n].obj m := beta (beta α j) i

-- two maps f and g are equal on the image of α iff
/- ∀ x, (f x ≠ g x → ∀ z, α z ≠ x) -/
/- ∀ x, (f x = g x ∨ ∀ z, α z ≠ x) -/
lemma foo {α β γ : Sort*} (f : α → β) (g h : β → γ) :
    g ∘ f = h ∘ f ↔ ∀ y, (g y = h y ∨ ∀ x, f x ≠ y) := by
  apply Iff.intro
  · intro p y
    by_cases he : ∃ x, f x = y
    · have x := Classical.choose he
      have hx := Classical.choose_spec he
      apply Or.inl
      rw [← hx]
      rw [← Function.comp_apply (f := g) (g := f)]
      rw [p]
      rfl
    · apply Or.inr
      simp at he
      exact he
  · intro p
    ext x
    rcases p (f x) with (p | p)
    · exact p
    · exact False.elim (p x rfl)

lemma bar {a b c : ℕ} (f : ([a] : SimplexCategory) ⟶ [b])
    (g h : ([b] : SimplexCategory) ⟶ [c]) :
    f ≫ g = f ≫ h ↔ ∀ y, (g.toOrderHom y = h.toOrderHom y ∨ ∀ x, f.toOrderHom x ≠ y) := by
  sorry

lemma baz {a b c : ℕ} (f : ([a] : SimplexCategory) ⟶ [b])
    (g h : ([b] : SimplexCategory) ⟶ [c]) :
    f ≫ g = f ≫ h ↔ ∀ y, (g.toOrderHom y ≠ h.toOrderHom y → ∀ x, f.toOrderHom x ≠ y) := by
  sorry
/- lemma predAbove_eq_lt_iff {p j : Fin n} (h : j < p) (i : Fin (n + 1)) : -/
/-     p.predAbove i = j ↔ i = j.castSucc := by -/

open Fin in
lemma factor_δ_spec' {m n : ℕ} (f : ([m] : SimplexCategory) ⟶ [n+1]) (j : Fin (n+2))
    (hj : ∀ (k : Fin (m+1)), f.toOrderHom k ≠ j) :
    factor_δ f j ≫ δ j = f := by
  ext k : 3
  specialize hj k
  dsimp [factor_δ, σ, δ]
  rcases hj.lt_or_lt with (hf | hf)
  · apply succAbove_eq_lt_iff hf _ |>.mpr
    rw [← succ_pred j (ne_zero_of_lt hf), predAbove_zero_succ]
    rw [← castPred_eq_iff_eq_castSucc _ (ne_last_of_lt hf) _ |>.mp _]
    rw [← succ_pred j (ne_zero_of_lt hf)] at hf
    exact predAbove_of_lt_succ _ _ hf |>.symm
  · apply succAbove_eq_gt_iff hf _ |>.mpr
    rw [← pred_eq_iff_eq_succ (ne_zero_of_lt hf) |>.mp _]
    cases' j using cases with j
    · exact predAbove_zero_of_ne_zero (ne_zero_of_lt hf) |>.symm
    · rw [predAbove_zero_succ]
      exact predAbove_of_succ_le _ _ (le_of_lt hf) |>.symm

  /- ext k : 3 -/
  /- specialize hj k -/
  /- dsimp [factor_δ, σ, δ] -/
  /- cases' j using cases with j -/
  /- · rw [predAbove_right_zero, zero_succAbove, succ_predAbove_zero] -/
  /-   exact hj -/
  /- · rw [predAbove_zero_succ] -/
  /-   rcases hj.lt_or_lt with (hf | hf) -/
  /-   · apply succAbove_eq_lt_iff hf _ |>.mpr -/
  /-     rw [predAbove_of_le_castSucc] -/
  /-     · rfl -/
  /-     · exact le_castSucc_iff.mpr hf -/
  /-   · apply succAbove_eq_gt_iff hf _ |>.mpr -/
  /-     rw [← succ_predAbove_succ] -/
  /-     exact predAbove_eq_gt_iff hf _ |>.mpr rfl -/

  /- nth_rewrite 2 [← Category.comp_id f] -/
  /- apply baz f (σ _ ≫ δ j) (𝟙 _) |>.mpr -/
  /- intro k hk x -/
  /- dsimp [σ, δ] at hk -/
  /- obtain hh | hh | hh : k < j ∨ j < k ∨ j = k := by omega -/
  /- · /1- rw [succAbove_eq_lt_iff hh _ |>.mpr] at hk -1/ -/
  /-   rw [not_iff_not.mpr (succAbove_eq_lt_iff hh _)] at hk -/
  /-   rw [predAbove_zero_of_ne_zero] at hk -/
  /-   swap -/
  /-   · exact ne_zero_of_lt hh -/
  /-   · rw [predAbove_castSucc_of_le (j.pred _)] at hk -/

open Fin in
lemma δ_gamma {n : ℕ} {m : SimplexCategoryᵒᵖ} (α : Δ[n + 2].obj m)
    {i : Fin (n + 2)} (hi : ∀ x, (asOrderHom α) x ≠ i.castSucc)
    {j : Fin (n + 3)} (hj : ∀ x, (asOrderHom α) x ≠ j) (h : i.castSucc < j) :
    (standardSimplex.map (δ i)).app m (gamma α i j) = beta α j := by
  simp [gamma, beta, standardSimplex, uliftFunctor]
  rw [predAbove_zero_of_ne_zero (ne_zero_of_lt h)]
  change factor_δ (m := m.unop.len) (_ ≫ σ _) i ≫ δ i = _
  apply factor_δ_spec
  intro k
  dsimp [σ, δ]
  obtain hlt | heq := lt_or_eq_of_le <| le_pred_iff _ |>.mpr h
  · rw [predAbove_eq_lt_iff hlt]
    exact hi k
  · rw [← heq, predAbove_eq_iff]
    rintro (hn | hn)
    · exact hi k hn
    · simp only [heq, succ_pred] at hn
      exact hj k hn


open Fin in
@[reassoc]
lemma bat {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 3)} (h : i.castSucc < j) :
    σ (predAbove 0 j) ≫ σ (predAbove 0 i) =
      σ (predAbove 0 i.castSucc) ≫ σ (predAbove 0 (j.pred (ne_zero_of_lt h))) := by
  rw [predAbove_zero_of_ne_zero (ne_zero_of_lt h)]
  /- rw [← castSucc_zero, castSucc_predAbove_castSucc] -/
  /- rw [σ_comp_σ] -/
  /- · -/ 
  /-   /1- ext k -1/ -/
  /-   /1- dsimp [σ] -1/ -/
  /-   obtain hlt | heq := lt_or_eq_of_le <| le_pred_iff (ne_zero_of_lt h) |>.mpr h -/
  /-   · rw [predAbove_zero_of_ne_zero (ne_zero_of_lt hlt)] -/
  /-     cases' i using cases with i -/
  /-     · simp only [predAbove_right_zero, succ_pred] -/
  /-     · rw [predAbove_zero_succ, succ_pred] -/
  /-   · rw [← heq] -/

  /-   sorry -/
  /- · obtain hlt | heq := lt_or_eq_of_le <| le_pred_iff (ne_zero_of_lt h) |>.mpr h -/
  /-   · rw [predAbove_zero_of_ne_zero (ne_zero_of_lt hlt)] -/
  /-     cases' i using cases with i -/
  /-     · simp only [predAbove_right_zero, Fin.zero_le] -/
  /-     · rw [predAbove_zero_succ] -/
  /-       exact le_pred_iff _ |>.mpr (le_of_lt hlt) -/
  /-   · rw [← heq] -/


  /- · obtain hlt | heq := lt_or_eq_of_le <| le_pred_iff (ne_zero_of_lt h) |>.mpr h -/
  /-   · rw [succ_predAbove_zero (ne_zero_of_lt hlt)] -/
  /-   · rw [← heq] -/
  /-     cases' i using cases with i -/
  /-     · simp -/
  /- · obtain hlt | heq := lt_or_eq_of_le <| le_pred_iff (ne_zero_of_lt h) |>.mpr h -/
  /-   · rw [predAbove_zero_of_ne_zero (ne_zero_of_lt hlt)] -/
  /-     cases' i using cases with i -/
  /-     · simp only [predAbove_right_zero, Fin.zero_le] -/
  /-     · rw [predAbove_zero_succ] -/
  /-       exact le_pred_iff _ |>.mpr (le_of_lt hlt) -/
  /-   · rw [← heq] -/


  obtain hlt | heq := lt_or_eq_of_le <| le_pred_iff (ne_zero_of_lt h) |>.mpr h
  · cases' i using cases with i
    · simp only [predAbove_right_zero, castSucc_zero]
      slice_rhs 1 1 => rw [← castSucc_zero]
      rw [σ_comp_σ (zero_le _)]
      rw [succ_predAbove_zero (ne_zero_of_lt hlt)]
    · slice_rhs 1 1 => rw [← succ_castSucc]
      simp only [predAbove_zero_succ]
      rw [predAbove_zero_of_ne_zero (ne_zero_of_lt hlt)]
      rw [σ_comp_σ (le_pred_iff _ |>.mpr (le_of_lt hlt))]
      rw [succ_pred]
  · rw [← heq]
    cases' i using cases with i
    · simp only [predAbove_right_zero, castSucc_zero]
    · rw [← succ_castSucc i]
      simp only [predAbove_zero_succ]
      exact σ_comp_σ le_rfl |>.symm

open Fin in
lemma δ_gamma' {n : ℕ} {m : SimplexCategoryᵒᵖ} (α : Δ[n + 2].obj m)
    {i : Fin (n + 2)} (hi : ∀ x, (asOrderHom α) x ≠ i.castSucc)
    {j : Fin (n + 3)} (hj : ∀ x, (asOrderHom α) x ≠ j) (h : i.castSucc < j) :
    (standardSimplex.map (δ (j.pred (ne_zero_of_lt h)))).app m (gamma α i j) =
      beta α i.castSucc := by
  simp [gamma, beta, standardSimplex, uliftFunctor]

  rw [bat_assoc h]
  change factor_δ (m := m.unop.len) (_ ≫ σ _) (j.pred _) ≫ δ _ = _
  rw [factor_δ_spec]
  intro k
  dsimp [σ]
  obtain hlt | heq := lt_or_eq_of_le <| le_pred_iff (ne_zero_of_lt h) |>.mpr h
  · cases' i using cases with i
    · simp only [castSucc_zero, predAbove_right_zero]
      erw [predAbove_zero_of_ne_zero (hi k)]
      rw [pred_inj]
      exact hj k
    · nth_rewrite 1 [← succ_castSucc i]
      rw [predAbove_zero_succ]
      intro hn
      have := predAbove_eq_gt_iff (lt_succ.trans hlt) _ |>.mp hn
      simp at this
      exact hj k this
  · rw [← heq]
    cases' i using cases with i
    · simp only [castSucc_zero, predAbove_right_zero]
      erw [predAbove_zero_of_ne_zero (hi k)]
      aesop
    · nth_rewrite 1 [← succ_castSucc]
      erw [predAbove_zero_succ]
      rw [predAbove_eq_gt_iff (castSucc_lt_succ i)]
      rw [heq, succ_pred]
      exact hj k

  /- ext k : 3 -/
  /- simp [σ, δ] -/

  /- #check factor_δ (_ ≫ σ (predAbove 0 i.castSucc)) -/
  /- #check factor_δ_spec (_ ≫ σ (predAbove 0 i.castSucc)) (j.pred _) -/
  /- #check factor_δ (m := m.unop.len) (_ ≫ σ (predAbove 0 i.castSucc)) (j.pred _) ≫ δ (j.pred _) -/
  -- Can we prove that lhs = factor_δ (α ≫ σ (predAbove 0 i.castSucc)) j.pred ≫ δ j.pred
  /- have hjp : i ≤ j.pred (ne_zero_of_lt h) := by -/
  /-   exact le_pred_iff (ne_zero_of_lt h) |>.mpr h -/
  /- rcases lt_or_eq_of_le hjp with (hjp | hjp) -/

  /- let jpred := j.pred <| ne_zero_of_lt h -/
  /- have hjp : jpred.succAbove ((predAbove 0 i).predAbove (jpred.predAbove -/
  /-     ((Hom.toOrderHom α.down) k))) ≠ jpred := by -/
  /-   sorry -/
  have hjp : (predAbove 0 i.castSucc).predAbove (asOrderHom α k) ≠
      j.pred (ne_zero_of_lt h) := by
    cases' i using cases with i
    · rw [predAbove_right_zero]

  rcases hjp.lt_or_lt with (hh | hh)
  · apply succAbove_eq_lt_iff hh _ |>.mpr
    rcases hi k |>.lt_or_lt with (ha | ha)
    · rw [predAbove_zero_of_ne_zero (ne_zero_of_lt ha)] at hh ⊢
      rw [predAbove_zero_of_ne_zero (castSucc_ne_zero_iff.mp (ne_zero_of_lt ha))]
      rw [predAbove_pred_of_lt _ _ ha] at hh ⊢
      rw [predAbove_eq_lt_iff hh _ |>.mpr (by rfl)]
      rw [predAbove_of_le_castSucc]
      · rw [castSucc_castPred]
      · exact (le_castSucc_pred_iff (castSucc_ne_zero_iff.mp (ne_zero_of_lt ha))).mpr ha
    · cases' i using cases with i
      · simp only [predAbove_right_zero, castSucc_zero] at hh ⊢
        rw [predAbove_zero_of_ne_zero (ne_zero_of_lt ha)] at hh ⊢
        erw [predAbove_pred_of_lt _ _ (pred_lt_pred_iff.mp hh)]
        rw [castSucc_zero] at hi
        rw [predAbove_zero_of_ne_zero]
        · rfl
        · exact castSucc_ne_zero_iff.mp (hi k)
      · rw [predAbove_zero_succ]
        /- rw [← succ_castSucc i] at hh -/
        /- rw [predAbove_zero_of_ne_zero (succ_ne_zero i)] -/
        rw [predAbove_pred_of_lt]
        · rw [← castSucc_predAbove_castSucc, castSucc_castPred]
          rw [← succ_castSucc] at ha
          erw [predAbove_of_succ_le _ _ (le_of_lt ha)]
          rw [← succ_castSucc, predAbove_zero_succ,
            predAbove_of_succ_le _ _ (le_of_lt ha)]
        · conv at hh => congr; rw [← succ_castSucc i]
          rw [← succ_castSucc] at ha
          rw [predAbove_zero_succ, predAbove_of_castSucc_lt _ _ (lt_succ.trans ha)] at hh
          exact pred_lt_pred_iff.mp hh
  · apply succAbove_eq_gt_iff hh _ |>.mpr
    sorry


    cases' i using cases with i
    · simp
      sorry
    · rw [predAbove_zero_succ]
      rw [← castPred_eq_iff_eq_castSucc _ (ne_last_of_lt hh) _ |>.mp _]
      symm
      apply predAbove_eq_lt_iff _ ((j.pred _).predAbove (asOrderHom α k)) |>.mpr
      · simp
        apply predAbove_eq_lt_iff hh _ |>.mpr
        rw [← succ_castSucc, predAbove_zero_succ]
        rcases (hi k).lt_or_lt with (ha | ha)
        · rw [predAbove_of_lt_succ _ _ ha, castSucc_castPred]
        · simp [predAbove]

      · sorry

      rcases (hi k).lt_or_lt with (ha | ha)
      · rw [← succ_castSucc] at ha
        #check predAbove_eq_lt_iff hh _ |>.mpr _
        rw [predAbove_of_lt_succ _ _ ha]

      /- #check predAbove_of_succ_le -/

      sorry
  · sorry

  rcases hj.lt_or_lt with (hf | hf)
  · apply succAbove_eq_lt_iff hf _ |>.mpr
    rw [← succ_pred j (ne_zero_of_lt hf), predAbove_zero_succ]
    rw [← castPred_eq_iff_eq_castSucc _ (ne_last_of_lt hf) _ |>.mp _]
    rw [← succ_pred j (ne_zero_of_lt hf)] at hf
    exact predAbove_of_lt_succ _ _ hf |>.symm
  · apply succAbove_eq_gt_iff hf _ |>.mpr
    rw [← pred_eq_iff_eq_succ (ne_zero_of_lt hf) |>.mp _]
    cases' j using cases with j
    · exact predAbove_zero_of_ne_zero (ne_zero_of_lt hf) |>.symm
    · rw [predAbove_zero_succ]
      exact predAbove_of_succ_le _ _ (le_of_lt hf) |>.symm



  rcases (hj k).lt_or_lt with (ha | ha)
  · rcases (hi k).lt_or_lt with (hb | hb)
    · rw [predAbove_zero_of_ne_zero (ne_zero_of_lt hb), predAbove_zero_of_ne_zero]
      swap
      · rintro rfl
        exact not_lt_zero _ hb
      · rw [predAbove_of_le_castSucc (j.pred _)]
        · rw [predAbove_of_le_castSucc]
          · rw [succAbove_of_castSucc_lt]
            · simp only [castSucc_castPred]
              rw [predAbove_of_le_castSucc]
              exact (le_castSucc_pred_iff (ne_zero_of_lt hb)).mpr hb
            · exact lt_of_lt_of_le hb ((le_castSucc_pred_iff (ne_zero_of_lt ha)).mpr h)
          · exact le_castSucc_pred_iff (ne_zero_of_lt hb) |>.mpr hb
        · exact (le_castSucc_pred_iff (Fin.ne_zero_of_lt h)).mpr ha
    · #check @succAbove_eq_lt_iff _ (j.pred _)
      sorry
  · rcases (hi k).lt_or_lt with (hb | hb)
    · omega
    · cases' i using cases with i
      · rw [succAbove_eq_gt_iff]
        · simp only [predAbove_right_zero, castSucc_zero]
          erw [predAbove_zero_of_ne_zero (ne_zero_of_lt ha)]
          rw [← succ_predAbove_succ]
          simp
          rw [predAbove_of_castSucc_lt]
          · sorry
          · sorry
        · simp only [castSucc_zero, predAbove_right_zero]
          erw [predAbove_zero_of_ne_zero (ne_zero_of_lt ha)]
          exact pred_lt_pred_iff.mpr ha
      · sorry

  /- let rhs := asOrderHom α k -/
  /- let jpred := j.pred (ne_zero_of_lt h) |>.castSucc -/
  /- obtain hh | hh | hh : rhs < jpred ∨ jpred < rhs ∨ rhs = jpred := by omega -/
  /- · have h' := castPred_lt_iff (ne_last_of_lt hh) |>.mpr hh -/
  /-   rw [succAbove_eq_lt_iff h' _ |>.mpr] -/
  /-   · cases' i using cases with i -/
  /-     · simp only [rhs, castSucc_zero, predAbove_right_zero] -/
  /-       erw [predAbove_zero_of_ne_zero (hi k)] -/

  rcases (hj k).lt_or_lt with (ha | ha)
  · erw [predAbove_of_le_castSucc _ _ <| le_castSucc_pred_iff (ne_zero_of_lt h) |>.mpr ha]
    cases' i using cases with i
    · simp
      sorry
    · simp
      rcases (hi k).lt_or_lt with (hb | hb)
      · rw [predAbove_of_le_castSucc]
        swap
        · exact le_castSucc_iff.mpr hb
        · rw [succAbove_of_castSucc_lt]
          swap
          · simp
            sorry
          · rw [predAbove_of_le_castSucc]
            · rfl
            · rw [predAbove_zero_of_ne_zero]
              · simp
                exact le_castSucc_iff.mpr hb
              · exact Fin.ne_zero_of_lt hb
      · rw [predAbove_of_castSucc_lt]
        · rw [succAbove_of_castSucc_lt]
          · sorry
          ·
        · sorry
  · sorry


  let jpred := j.pred (ne_zero_of_lt h)
  obtain hh | hh : (predAbove 0 i).castSucc < jpred ∨ (predAbove 0 i).castSucc = jpred := by sorry
  · simp [jpred] at hh
    rw [← δ_comp_σ_of_gt hh, succ_pred]
    rw [← Category.assoc]
    change factor_δ (m := m.unop.len) _ j ≫ δ j ≫ _ = _
    rw [← Category.assoc]
    rw [factor_δ_spec _ _ hj]
    rw [← castSucc_zero, castSucc_predAbove_castSucc]
  · simp [jpred] at hh
    rw [predAbove_zero_of_ne_zero (ne_zero_of_lt h)]
    rw [← hh]
    rw [σ_comp_σ_assoc (by rfl)]
    change factor_δ (m := m.unop.len) (_ ≫ σ _) _ ≫ δ _ = _
    cases' i using cases with i
    · simp
      rw [factor_δ_spec]
      · ext k : 3
        simp [σ]

        sorry
        -- should be able to say that α ≫ σ _ = α ↔ α doesn't touch _
      · intro k
        simp
        intro h0
        exact hi k <| σ_eq_lt_iff zero_lt_one _ |>.mp h0
    · simp
      simp [factor_δ]
      rw [← castSucc_predAbove_castSucc, castSucc_zero] at hh
      have h' : 0 < jpred := by
        have h'' : i.castSucc < j.pred (ne_zero_of_lt h) := by
          exact (lt_pred_iff (Fin.ne_zero_of_lt h)).mpr h
        exact pos_of_ne_zero <| ne_zero_of_lt h''
      ext k : 3
      simp
      rw [predAbove_eq_gt_iff h' _ |>.mp hh] at h
      simp [jpred] at h

  simp [δ, σ]
  rw [← castSucc_zero]
  rw [castSucc_predAbove_castSucc 0 i]
  #check (asOrderHom α k)
  #check @predAbove_eq_lt_iff _ (j.pred _)

  /- let jpred := j.pred (ne_zero_of_lt h) -/
  /- obtain hlt | heq : i < jpred ∨ i = jpred := lt_or_eq_of_le <| le_pred_iff _ |>.mpr h -/
  /- · sorry -/
  /- · simp [jpred] at heq -/
  /-   rw [← heq] -/
  /-   change factor_δ (m := m.unop.len) (_ ≫ σ _) i ≫ δ i = _ -/
  /-   rw [factor_δ_spec] -/

  /- let jpred := j.pred (ne_zero_of_lt h) |>.castSucc -/
  let jpred := j.pred (ne_zero_of_lt h)
  let rhs := (predAbove 0 i.castSucc).predAbove (asOrderHom α k)
  obtain hlt | hgt | heq : jpred < rhs ∨ rhs < jpred ∨ jpred = rhs := by omega
    /- jpred < asOrderHom α k ∨ asOrderHom α k < jpred ∨ jpred = asOrderHom α k := by omega -/
  · simp only [jpred, rhs] at hlt
    apply succAbove_eq_gt_iff hlt _ |>.mpr
    /- rw [← succ_predAbove_succ] -/
    cases' i using cases with i
    · simp at hlt ⊢
      rw [succ_predAbove_zero]
    sorry
  · simp [jpred, rhs] at hgt
    apply succAbove_eq_lt_iff hgt _ |>.mpr
    sorry
  · simp [jpred, rhs] at heq



  /- simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply] -/
  cases' i using cases with i
  · rw [predAbove_right_zero]
    simp
    rcases (hj k).lt_or_lt with (ha | ha)
    · have hh : (asOrderHom α) k ≤ (j.pred (ne_zero_of_lt h)).castSucc :=
        (le_castSucc_pred_iff (Fin.ne_zero_of_lt h)).mpr ha
      dsimp [σ, δ]
      erw [predAbove_of_le_castSucc _ _ hh]
      /- change (δ _).toOrderHom ((σ _).toOrderHom _) = (σ _).toOrderHom _ -/
      rw [predAbove_zero_of_ne_zero]
      swap
      · exact castSucc_ne_zero_iff.mp (hi k)
      · apply succAbove_eq_lt_iff _ _ |>.mpr
        · erw [predAbove_zero_of_ne_zero (hi k)]
          rfl
        · erw [predAbove_zero_of_ne_zero (hi k)]
          exact pred_lt_pred_iff.mpr ha
    ·

  · rw [predAbove_zero_succ]
    rw [← δ_comp_σ_of_gt ((lt_pred_iff _).mpr h)]
    rw [succ_pred]
    simp
    rcases (hj k).lt_or_lt with (ha | ha)
    · have hh : (asOrderHom α) k ≤ (j.pred (ne_zero_of_lt h)).castSucc :=
        (le_castSucc_pred_iff (Fin.ne_zero_of_lt h)).mpr ha
      dsimp [σ, δ]
      erw [predAbove_of_le_castSucc _ _ hh]
      change (σ _).toOrderHom ((δ _).toOrderHom _) = (σ _).toOrderHom _
      rw [δ_eq_lt_iff ha _ |>.mpr (by rfl)]
      rw [← succ_castSucc, predAbove_zero_succ]
      rfl
    · have hh : (j.pred (ne_zero_of_lt h)).castSucc < asOrderHom α k :=
        castSucc_pred_lt_iff _ |>.mpr (le_of_lt ha)
      /- #check σ_eq_gt_iff hh -/
      /- #check @σ_eq_gt_iff _ (j.pred _) _ _ (asOrderHom α k) -/
      dsimp [σ, δ]
      erw [predAbove_of_castSucc_lt _ _ hh]
      change (σ _).toOrderHom ((δ _).toOrderHom _) = (σ _).toOrderHom _
      rw [δ_eq_gt_iff ha _ |>.mpr (by simp)]
      rw [← succ_castSucc, predAbove_zero_succ]
      rfl

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

set_option pp.coercions false
open Fin standardSimplex Opposite in
lemma beta_pi {n : ℕ} (X : Multicofork (diagram n))
    {m : SimplexCategoryᵒᵖ} (α : Δ[n + 2].obj m)
    (i : Fin (n + 3)) (hi : ∀ x, (asOrderHom α) x ≠ i)
    (j : Fin (n + 3)) (hj : ∀ x, (asOrderHom α) x ≠ j) :
    (X.π i).app m (beta α i) = (X.π j).app m (beta α j) := by
  obtain rfl | hij | hji : i = j ∨ i < j ∨ j < i := by omega
  · rfl
  · let i' : Fin (n + 2) := i.castPred <| Fin.ne_last_of_lt hij
    have hi' : i = i'.castSucc := by aesop
    let ij : { (i, j) : Fin (n + 2) × Fin (n + 3) | i.castSucc < j } :=
      ⟨(i', j), hij⟩
    let γ := gamma α i' j
    rw [hi'] at hi
    have hu : ((diagram n).snd ij).app m γ = beta α j := δ_gamma α hi hj hij
    have hv : ((diagram n).fst ij).app m γ = beta α i := δ_gamma' α hi hj hij
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
