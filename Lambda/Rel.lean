import Lambda.Prelude
import Mathlib.Tactic.Relation.Trans

def Rel (T : Type u) := T → T → Prop

namespace Rel

variable {R : Rel T} {R₁ : Rel T₁} {R₂ : Rel T₂} {R₃ : Rel T₃}

@[aesop safe [constructors]]
inductive Multi (R : Rel T) : Rel T where
| refl : R.Multi t t
| step : R t₁ t₂ → R.Multi t₂ t₃ → R.Multi t₁ t₃

namespace Multi

@[trans] theorem trans : R.Multi t₁ t₂ → R.Multi t₂ t₃ → R.Multi t₁ t₃ := by
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
  trans f t₁' t₂
  · apply congr h₁; aesop
  · apply congr h₂; aesop

theorem congr₃ {f : T₁ → T₂ → T₃ → T} :
  R₁.Multi t₁ t₁' → R₂.Multi t₂ t₂' → R₃.Multi t₃ t₃' →
  (∀ {t₁ t₁' t₂ t₃}, R₁ t₁ t₁' → R (f t₁ t₂ t₃) (f t₁' t₂ t₃)) →
  (∀ {t₁ t₂ t₂' t₃}, R₂ t₂ t₂' → R (f t₁ t₂ t₃) (f t₁ t₂' t₃)) →
  (∀ {t₁ t₂ t₃ t₃'}, R₃ t₃ t₃' → R (f t₁ t₂ t₃) (f t₁ t₂ t₃')) →
  R.Multi (f t₁ t₂ t₃) (f t₁' t₂' t₃') := by
  intros h₁ h₂ h₃ h h' h''
  trans f t₁' t₂ t₃
  · apply congr h₁; aesop
  trans f t₁' t₂' t₃
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

theorem StrongNormal.no_infinite_reduce :
  R.StrongNormal t →
  ¬ ∃ (f : Nat → T), f 0 = t ∧ ∀ n, R (f n) (f (n + 1)) := by
  intro h; induction' h with t _ ih
  intro ⟨f, h₁, h₂⟩
  apply ih
  · rw [←h₁]; apply h₂
  · aesop

end Rel
