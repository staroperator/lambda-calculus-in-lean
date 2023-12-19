import Mathlib.Order.Iterate
import Lambda.Prelude

def Rel (T : Type u) := T → T → Prop

namespace Rel

variable {R : Rel T} {R₁ : Rel T₁} {R₂ : Rel T₂} {R₃ : Rel T₃}

@[aesop safe [constructors]]
inductive Multi (R : Rel T) : Rel T where
| refl : R.Multi t t
| step : R t₁ t₂ → R.Multi t₂ t₃ → R.Multi t₁ t₃

namespace Multi

theorem trans : R.Multi t₁ t₂ → R.Multi t₂ t₃ → R.Multi t₁ t₃ := by
  intros h₁ h₂
  induction h₁ <;> aesop

theorem congr {f : T₁ → T} :
  R₁.Multi t₁ t₂ →
  (∀ {t₁ t₂}, R₁ t₁ t₂ → R (f t₁) (f t₂)) →
  R.Multi (f t₁) (f t₂) := by
  intros h₁ h
  induction h₁ with
  | refl => constructor
  | step h₁ _ ih => aesop

theorem congr₂ {f : T₁ → T₂ → T} :
  R₁.Multi t₁ t₁' → R₂.Multi t₂ t₂' →
  (∀ {t₁ t₁' t₂}, R₁ t₁ t₁' → R (f t₁ t₂) (f t₁' t₂)) →
  (∀ {t₂ t₂' t₁}, R₂ t₂ t₂' → R (f t₁ t₂) (f t₁ t₂')) →
  R.Multi (f t₁ t₂) (f t₁' t₂') := by
  intros h₁ h₂ h h'
  apply trans (t₂ := f t₁' t₂)
  · apply congr h₁; aesop
  · apply congr h₂; aesop

theorem congr₃ {f : T₁ → T₂ → T₃ → T} :
  R₁.Multi t₁ t₁' → R₂.Multi t₂ t₂' → R₃.Multi t₃ t₃' →
  (∀ {t₁ t₁' t₂ t₃}, R₁ t₁ t₁' → R (f t₁ t₂ t₃) (f t₁' t₂ t₃)) →
  (∀ {t₁ t₂ t₂' t₃}, R₂ t₂ t₂' → R (f t₁ t₂ t₃) (f t₁ t₂' t₃)) →
  (∀ {t₁ t₂ t₃ t₃'}, R₃ t₃ t₃' → R (f t₁ t₂ t₃) (f t₁ t₂ t₃')) →
  R.Multi (f t₁ t₂ t₃) (f t₁' t₂' t₃') := by
  intros h₁ h₂ h₃ h h' h''
  apply trans (t₂ := f t₁' t₂ t₃)
  · apply congr h₁; aesop
  apply trans (t₂ := f t₁' t₂' t₃)
  · apply congr h₂; aesop
  · apply congr h₃; aesop

end Multi

def Diamond (R : Rel T) :=
  ∀ {t t₁ t₂}, R t t₁ → R t t₂ → ∃ t', R t₁ t' ∧ R t₂ t'

lemma Multi.stripe : R.Diamond →
  R t t₁ → R.Multi t t₂ → ∃ t', R.Multi t₁ t' ∧ R t₂ t' := by
  intros h h₁ h₂
  induction h₂ generalizing t₁ with
  | refl => exists t₁, Multi.refl
  | step h₂ _ ih =>
    rcases h h₁ h₂ with ⟨t', h₃, h₄⟩
    rcases ih h₄ with ⟨t'', h₅, h₆⟩
    exists t''; aesop

theorem Multi.diamond : R.Diamond → R.Multi.Diamond := by
  intros h t t₁ t₂ h₁ h₂
  induction h₁ generalizing t₂ with
  | refl => exists t₂, h₂; exact Multi.refl
  | step h₁ _ ih =>
    rcases stripe h h₁ h₂ with ⟨t', h₃, h₄⟩
    rcases ih h₃ with ⟨t'', h₅, h₆⟩
    exists t''; aesop

inductive Equiv (R : Rel T) : Rel T where
| refl : R.Equiv t t
| symm : R.Equiv t₁ t₂ → R.Equiv t₂ t₁
| trans : R.Equiv t₁ t₂ → R.Equiv t₂ t₃ → R.Equiv t₁ t₃
| step : R t₁ t₂ → R.Equiv t₁ t₂

theorem Equiv.of_multi : R.Multi t₁ t₂ → R.Equiv t₁ t₂ := by
  intro h
  induction h with
  | refl => exact Equiv.refl
  | step h _ ih => exact Equiv.trans (Equiv.step h) ih

theorem Equiv.iff_multi_same :
  R.Multi.Diamond → (R.Equiv t₁ t₂ ↔ ∃ t, R.Multi t₁ t ∧ R.Multi t₂ t) := by
  intro h; constructor
  · intro h₁
    induction h₁ with
    | @refl t => exists t; constructor <;> exact Multi.refl
    | symm _ ih => rcases ih with ⟨t, h₁, h₂⟩; exists t
    | trans _ _ ih₁ ih₂ =>
      rcases ih₁ with ⟨t, h₁, h₂⟩
      rcases ih₂ with ⟨t', h₃, h₄⟩
      rcases h h₂ h₃ with ⟨t'', h₅, h₆⟩
      exists t''
      constructor <;> apply Multi.trans <;> assumption
    | @step t₁ t₂ h₁ =>
      exists t₂; constructor
      · exact Multi.step h₁ Multi.refl
      · exact Multi.refl
  · intro ⟨t, h₁, h₂⟩
    apply Equiv.trans
    · exact (Equiv.of_multi h₁)
    · exact (Equiv.symm (Equiv.of_multi h₂))

def Normal (R : Rel T) (t : T) := ∀ t', ¬ R t t'

theorem Normal.multi_eq : R.Normal t → R.Multi t t' → t' = t := by
  intros h₁ h₂
  cases h₂ with
  | refl => rfl
  | step h₂ h₃ => exfalso; apply h₁; exact h₂

theorem Normal.uniqueness :
  R.Multi.Diamond → R.Multi t t₁ → R.Multi t t₂ → R.Normal t₁ → R.Normal t₂ → R.Equiv t₁ t₂ := by
  intros h h₁ h₂ h₃ h₄
  rcases h h₁ h₂ with ⟨t', h₅, h₆⟩
  apply multi_eq h₃ at h₅
  apply multi_eq h₄ at h₆
  rw [←h₅, ←h₆]
  exact Equiv.refl

def WeakNormal (R : Rel T) (t : T) :=
  ∃ t', R.Multi t t' ∧ R.Normal t'

theorem WeakNormal.of_normal : R.Normal t → R.WeakNormal t := by
  intro h; exists t; constructor
  · constructor
  · exact h

theorem WeakNormal.reverse_step :
  R t t' → R.WeakNormal t' → R.WeakNormal t := by
  intro h ⟨t'', h₁, h₂⟩
  exists t''; aesop

inductive StrongNormal (R : Rel T) : T → Prop where
| sn : (∀ t', R t t' → R.StrongNormal t') → R.StrongNormal t

theorem StrongNormal.of_normal : R.Normal t → R.StrongNormal t := by
  intro h; constructor; intros; exfalso; aesop

theorem StrongNormal.step :
  R t t' → R.StrongNormal t → R.StrongNormal t' := by
  intro h ⟨h₁⟩; aesop

theorem StrongNormal.weak_normal : R.StrongNormal t → R.WeakNormal t := by
  intro h; induction' h with t _ ih
  rcases Classical.exists_or_forall_not (R t) with ⟨t', h⟩ | h
  · apply WeakNormal.reverse_step h
    apply ih; exact h
  · exact WeakNormal.of_normal h

theorem StrongNormal.iff_no_infinite_sequence :
  R.StrongNormal t ↔
  ¬ ∃ (f : Nat → T), f 0 = t ∧ ∀ n, R (f n) (f (n + 1)) := by
  constructor
  · intro h; induction' h with t _ ih
    intro ⟨f, h₁, h₂⟩
    apply ih
    · rw [←h₁]; apply h₂
    · aesop
  · intro h₁; by_contra h₂; apply h₁
    let T' := { t // ¬ R.StrongNormal t }
    let next (t : T') : T' := by
      apply Classical.choose (p := λ t' => R t.val t'.val)
      by_contra h₁
      apply forall_not_of_not_exists at h₁
      rcases t with ⟨t, h⟩
      apply h
      constructor
      intro t' h₂
      by_contra h₃
      have h₄ := h₁ ⟨t', h₃⟩
      contradiction
    let seq (n : Nat) : T' :=
      n.recAuxOn ⟨t, h₂⟩ (λ _ ih => next ih)
    exists λ n => (seq n).val
    constructor
    · rfl
    · intro n
      apply Classical.choose_spec (p := λ _ => R _ _)

theorem StrongNormal.strong_induction {P : T → Prop} :
  R.StrongNormal t → 
  ((∀ {t}, (∀ t' t'', R t t' → R.Multi t' t'' → P t'') → P t)) →
  P t := by
  intro h₁ h
  suffices h₂ : (∀ t', R.Multi t t' → P t') by
    apply h₂; constructor
  intro t' h₂
  induction' h₁ with t _ ih generalizing t'
  cases h₂ with
  | refl =>
    apply h
    intro t' t'' h₁ h₂
    apply ih
    · exact h₁
    · exact h₂
  | step h₂ h₂' =>
    apply ih
    · exact h₂
    · exact h₂'

inductive StrongNormal' (R : Rel T) : Nat → T → Prop where
| sn : (∀ t', R t t' → R.StrongNormal' k t') → R.StrongNormal' (k + 1) t

theorem StrongNormal'.strong_normal : R.StrongNormal' k t → R.StrongNormal t := by
  intro h
  induction' h with t _ _ ih
  constructor
  intros t' h
  apply ih
  exact h

theorem StrongNormal'.step : R t t' → R.StrongNormal' k t → ∃ k' < k, R.StrongNormal' k' t' := by
  intro h ⟨h₁⟩; aesop

theorem StrongNormal'.le : k ≤ k' → R.StrongNormal' k t → R.StrongNormal' k' t := by
  intros h h₁
  induction' h₁ with t _ _ ih generalizing k'
  cases k'
  · simp [Nat.not_succ_le_zero] at h
  · simp [Nat.succ_le_succ_iff] at h
    constructor; aesop

def Finite (R : Rel T) :=
  ∀ t, ∃ (l : List T), ∀ t', R t t' ↔ t' ∈ l

theorem StrongNormal.strong_normal' :
  R.Finite → R.StrongNormal t → ∃ k, R.StrongNormal' k t := by
  intro h h₁
  induction' h₁ with t _ ih₁
  rcases h t with ⟨l, h₁⟩
  have h₂ : ∀ t' ∈ l, ∃ k, R.StrongNormal' k t' := by
    intro t' h₃
    apply ih₁
    rw [h₁]
    exact h₃
  have h₃ : ∃ k, ∀ t' ∈ l, R.StrongNormal' k t' := by
    clear h₁ ih₁
    induction' l with t' l ih₂
    · exists 0; aesop
    · rcases h₂ t' (List.Mem.head _) with ⟨k₁, h₃⟩
      have h₄ : ∀ t' ∈ l, ∃ k, StrongNormal' R k t' := by
        intro t' h
        rcases h₂ t' (List.Mem.tail _ h) with ⟨k, h'⟩
        exists k
      apply ih₂ at h₄
      rcases h₄ with ⟨k₂, h₄⟩
      exists max k₁ k₂
      intro t'' h
      cases h
      · exact StrongNormal'.le (Nat.le_max_left _ _) h₃
      · apply StrongNormal'.le (Nat.le_max_right _ _)
        apply h₄
        assumption
  rcases h₃ with ⟨k, h₃⟩
  exists k + 1
  constructor
  intro t' h
  apply h₃
  rw [←h₁]
  exact h

def Deterministic (R : Rel T) :=
  ∀ t t₁ t₂, R t t₁ → R t t₂ → t₁ = t₂

theorem Deterministic.finite : R.Deterministic → R.Finite := by
  intro h t
  rcases Classical.exists_or_forall_not (R t) with ⟨t', h₁⟩ | h₁
  · exists [t']
    intro t''; constructor
    · intro h₂
      rw [h _ _ _ h₁ h₂]
      simp
    · intro h₂
      simp at h₂; rw [h₂]
      exact h₁
  · exists []
    intro t''; constructor
    · intro h₂; exfalso; apply h₁; exact h₂
    · intro h₂; cases h₂

theorem Deterministic.diamond : R.Deterministic → R.Multi.Diamond := by
  intro h t t₁ t₂ h₁ h₂
  induction h₁ with
  | refl => exact ⟨_, h₂, Multi.refl⟩
  | step h₁ h₁' ih =>
    cases h₂ with
    | refl => exact ⟨_, Multi.refl, Multi.step h₁ h₁'⟩
    | step h₂ h₂' =>
      have h₃ := h _ _ _ h₁ h₂
      subst h₃
      exact ih h₂'

lemma newman :
  (∀ t, R.StrongNormal t) →
  (∀ t t₁ t₂, R t t₁ → R t t₂ → ∃ t', R.Multi t₁ t' ∧ R.Multi t₂ t') →
  R.Multi.Diamond := by
  intro h h' t t₁ t₂ h₁ h₂
  induction' h t with t _ ih generalizing t₁ t₂
  cases h₁ with
  | refl => exact ⟨_, h₂, Multi.refl⟩
  | step h₁ h₁' =>
    cases h₂ with
    | refl => exact ⟨_, Multi.refl, Multi.step h₁ h₁'⟩
    | step h₂ h₂' =>
      rcases h' _ _ _ h₁ h₂ with ⟨t₃, h₃, h₄⟩
      rcases ih _ h₁ h₁' h₃ with ⟨t₄, h₅, h₆⟩
      rcases ih _ h₂ h₂' (Multi.trans h₄ h₆) with ⟨t', h₇, h₈⟩
      exists t'; constructor
      · exact Multi.trans h₅ h₈
      · exact h₇

end Rel
