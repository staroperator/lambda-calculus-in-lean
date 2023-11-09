import Stlc.Reduce

def WeakNormal (t : Term n) := ∃ t', t ⟶* t' ∧ Normal t'

inductive StrongNormal : Term n → Prop
| sn : (∀ t', t ⟶ t' → StrongNormal t') → StrongNormal t

theorem StrongNormal.weak_normal : StrongNormal t → WeakNormal t := by
  intro h
  induction' h with t _ ih
  rcases progress t with h₁ | ⟨t', h₁⟩
  · exact ⟨t, ⟨MultiStep.refl, h₁⟩⟩
  · rcases ih _ h₁ with ⟨t', h₂, h₃⟩
    exists t'
    constructor
    · constructor <;> assumption
    · assumption

theorem StrongNormal.iff_no_infinite_reduction {t : Term n} :
  StrongNormal t →
  ¬ ∃ (f : Nat → Term n), f 0 = t ∧ ∀ i, f i ⟶ f (i + 1) := by
  intro h
  induction' h with t _ ih
  rintro ⟨f, h₁, h₂⟩
  apply ih
  · rw [←h₁]
    apply h₂
  · exists λ i => f (i + 1)
    constructor
    · simp
    · intro; apply h₂

lemma StrongNormal.bool : StrongNormal (Term.bool b : Term n) := by
  constructor
  intro _ h
  cases h

theorem StrongNormal.step : t ⟶ t' → StrongNormal t → StrongNormal t' := by
  intros h₁ h₂
  cases' h₂ with _ h
  apply h
  exact h₁

lemma StrongNormal.weaken :
  StrongNormal t → StrongNormal (t[ρ]ʷ) := by
  intro h
  induction' h with t _ ih
  constructor
  intros _ h
  apply Step.inversion_weaken at h
  rcases h with ⟨t', h, h'⟩
  subst h'
  apply ih
  exact h

lemma StrongNormal.strengthen :
  StrongNormal (t[ρ]ʷ) → StrongNormal t := by
  intro h₁
  generalize h₂ : t[ρ]ʷ = t' at h₁
  induction' h₁ with _ _ ih generalizing t
  subst h₂
  constructor
  intros t' h
  apply ih
  · apply Step.weaken; exact h
  · rfl

lemma StrongNormal.inversion_app :
  StrongNormal (t₁ ⬝ t₂) → StrongNormal t₁ := by
  intro h₁
  generalize h₂ : t₁ ⬝ t₂ = t at h₁
  induction' h₁ with _ _ ih generalizing t₁ t₂
  subst h₂
  constructor
  intros t' h
  apply ih
  · apply Step.app₁; exact h
  · rfl

lemma StrongNormal.inversion_fst :
  StrongNormal t.fst → StrongNormal t := by
  intro h₁
  generalize h₂ : t.fst = t' at h₁
  induction' h₁ with _ _ ih generalizing t
  subst h₂
  constructor
  intros t' h
  apply ih
  · apply Step.fst; exact h
  · rfl



-- References:
-- https://github.com/AndrasKovacs/misc-stuff/blob/master/agda/STLCStrongNorm/StrongNorm.agda
-- https://abella-prover.org/examples/lambda-calculus/normalization/stlc-strong-norm.html
-- https://www.paultaylor.eu/stable/prot.pdf

def KripkeSem (Γ : Context n) (t : Term n) : Ty → Prop
| Ty.bool => StrongNormal t
| T₁ ⇒ T₂ => ∀ m (ρ : Weaken n m) Δ t',
  Γ ⊆[ρ] Δ → KripkeSem Δ t' T₁ → KripkeSem Δ (t[ρ]ʷ ⬝ t') T₂
| T₁ * T₂ => KripkeSem Γ t.fst T₁ ∧ KripkeSem Γ t.snd T₂
notation:50 Γ " ⊨ " t " : " T:50 => KripkeSem Γ t T

def Subst.KripkeSem (Γ : Context m) (σ : Subst n m) (Δ : Context n) :=
  ∀ x, Γ ⊨ σ x : Δ.get x
notation:50 Γ " ⊨ " σ " :ₛ " Δ:50 => Subst.KripkeSem Γ σ Δ

lemma KripkeSem.weaken {t : Term n} :
  Γ ⊆[ρ] Δ → Γ ⊨ t : T → Δ ⊨ t[ρ]ʷ : T := by
  intros h₁ h₂
  induction T generalizing n with
  | bool => exact StrongNormal.weaken h₂
  | fn T₁ T₂ =>
    intros k ρ' Θ t' h₃ h₄
    simp [Term.weaken_comp]
    apply h₂
    · exact Context.weaken_comp h₁ h₃
    · exact h₄
  | prod T₁ T₂ ih₁ ih₂ =>
    rcases h₂ with ⟨h₂, h₂'⟩
    constructor
    · apply ih₁ (t := t.fst) <;> assumption
    · apply ih₂ (t := t.snd) <;> assumption

lemma KripkeSem.step {t : Term n} :
  t ⟶ t' → Γ ⊨ t : T → Γ ⊨ t' : T := by
  intros h₁ h₂
  induction T generalizing n with
  | bool => exact StrongNormal.step h₁ h₂
  | fn T₁ T₂ _ ih₂ =>
    intros m ρ Δ t'' h₃ h₄
    apply ih₂
    · constructor
      apply Step.weaken
      exact h₁
    · apply h₂ <;> assumption
  | prod T₁ T₂ ih₁ ih₂ =>
    rcases h₂ with ⟨h₂, h₂'⟩
    constructor
    · apply ih₁
      · constructor; exact h₁
      · exact h₂
    · apply ih₂
      · constructor; exact h₁
      · exact h₂'

def Neutral : Term n → Prop
| λ' _ _ | ⟪_, _⟫ => False
| _ => True

mutual
open Fin'
theorem KripkeSem.strong_normal :
  Γ ⊨ t : T → StrongNormal t := by
  intro h
  match T with
  | Ty.bool => exact h
  | Ty.fn T₁ T₂ =>
    have h₁ : Γ,' T₁ ⊨ ↑ₜt ⬝ #fz : T₂ := by
      apply h
      · apply Context.Weaken.step
        apply Context.weaken_id
      · apply KripkeSem.neutral_reducible
        · constructor
        · intro _ h; cases h
    apply KripkeSem.strong_normal (T := T₂) at h₁
    apply StrongNormal.inversion_app at h₁
    apply StrongNormal.strengthen at h₁
    exact h₁
  | Ty.prod T₁ T₂ =>
    apply StrongNormal.inversion_fst
    apply KripkeSem.strong_normal
    exact h.left
theorem KripkeSem.neutral_reducible :
  Neutral t → (∀ t', t ⟶ t' → Γ ⊨ t' : T) → Γ ⊨ t : T := by
  intros h₁ h₂
  match T with
  | Ty.bool => constructor; exact h₂
  | Ty.fn T₁ T₂ =>
    intros m ρ Δ t' h₃ h₄
    have h₅ := KripkeSem.strong_normal h₄
    induction' h₅ with t' _ ih
    apply KripkeSem.neutral_reducible
    · constructor
    · intros t'' h₅
      generalize h₆ : t[ρ]ʷ = t₁ at h₅
      cases h₅ with
      | app₁ h₅ =>
        subst h₆
        apply Step.inversion_weaken at h₅
        rcases h₅ with ⟨t₁', h₅, h₆⟩
        subst h₆
        apply h₂ <;> assumption
      | app₂ h₅ =>
        subst h₆
        apply ih
        · exact h₅
        · exact KripkeSem.step h₅ h₄
      | beta =>
        cases t <;> simp at h₆
        contradiction
  | Ty.prod T₁ T₂ =>
    constructor
    · apply KripkeSem.neutral_reducible
      · constructor
      · intros t' h₃
        cases h₃ with
        | fst h₃ => apply h₂ at h₃; exact h₃.left
        | sigma₁ => cases h₁
    · apply KripkeSem.neutral_reducible
      · constructor
      · intros t' h₃
        cases h₃ with
        | snd h₃ => apply h₂ at h₃; exact h₃.right
        | sigma₂ => cases h₁
end

lemma KripkeSem.var : Γ ⊨ #x : Γ.get x := by
  apply KripkeSem.neutral_reducible
  · constructor
  · intros _ h; cases h

lemma KripkeSem.lam :
  StrongNormal t →
  (∀ m (t' : Term m) ρ Δ, Γ ⊆[ρ] Δ → Δ ⊨ t' : T₁ → Δ ⊨ t[⇑ʷρ]ʷ[↦ t'] : T₂) →
  Γ ⊨ λ' T₁ t : T₁ ⇒ T₂ := by
  intros h₁ h₂ m ρ Δ t' h₃ h₄
  simp
  induction' h₁ with t _ ih₁
  induction' KripkeSem.strong_normal h₄ with t' _ ih₂
  apply KripkeSem.neutral_reducible
  · constructor
  · intros t'' h₅
    cases h₅ with
    | app₁ h₅ =>
      cases h₅ with | lam h₅ =>
      apply Step.inversion_weaken at h₅
      rcases h₅ with ⟨t', h₅, h₆⟩
      subst h₆
      apply ih₁ _ h₅
      intros m t'' ρ Δ h h'
      apply KripkeSem.step
      · apply Step.subst; apply Step.weaken; exact h₅
      · apply h₂ <;> assumption
    | app₂ h₅ =>
      apply ih₂ _ h₅
      · exact KripkeSem.step h₅ h₄
      · intros t'' h h'
        apply KripkeSem.step
        · exact Step.app₂ h₅
        · apply ih₁ <;> assumption
    | beta => apply h₂ <;> assumption

lemma KripkeSem.pair :
  Γ ⊨ t₁ : T₁ → Γ ⊨ t₂ : T₂ → Γ ⊨ ⟪t₁, t₂⟫ : T₁ * T₂ := by
  intros h₁ h₂
  induction' KripkeSem.strong_normal h₁ with t₁ _ ih₁
  induction' KripkeSem.strong_normal h₂ with t₂ _ ih₂
  constructor
  · apply KripkeSem.neutral_reducible
    · constructor
    · intros t' h
      cases h with
      | sigma₁ => exact h₁
      | fst h =>
        cases h with
        | pair₁ h =>
          apply And.left; apply ih₁
          · exact h
          · exact KripkeSem.step h h₁
        | pair₂ h =>
          apply And.left; apply ih₂
          · exact h
          · exact KripkeSem.step h h₂
          · intros; apply KripkeSem.step
            · exact Step.pair₂ h
            · apply ih₁ <;> assumption
  · apply KripkeSem.neutral_reducible
    · constructor
    · intros t' h
      cases h with
      | sigma₂ => exact h₂
      | snd h =>
        cases h with
        | pair₁ h =>
          apply And.right; apply ih₁
          · exact h
          · exact KripkeSem.step h h₁
        | pair₂ h =>
          apply And.right; apply ih₂
          · exact h
          · exact KripkeSem.step h h₂
          · intros; apply KripkeSem.step
            · exact Step.pair₂ h
            · apply ih₁ <;> assumption

theorem KripkeSem.fundamental {σ : Subst n m} :
  Γ ⊢ t : T → Δ ⊨ σ :ₛ Γ → Δ ⊨ t[σ] : T := by
  intros h₁ h₂
  induction h₁ generalizing m <;> simp
  case var => apply h₂
  case lam _ _ T₁ _ _ _ ih =>
    apply KripkeSem.lam
    · apply KripkeSem.strong_normal
      apply ih (Δ := Δ,' T₁)
      intro x
      cases x
      · apply KripkeSem.var
      · simp [Context.get, Subst.lift]
        apply KripkeSem.weaken
        · constructor; apply Context.weaken_id
        · apply h₂
    · intros k t' ρ Θ h₃ h₄
      simp [Term.subst_comp_weaken, Term.subst_comp]
      apply ih
      intro x
      cases x
      · simp [Subst.comp, Subst.single, Context.get]
        exact h₄
      · simp [Subst.comp, Subst.lift, Context.get]
        rw [Weaken.lift_of_subst, Term.shift_subst_lift, Term.shift_subst_single, ←Term.weaken_eq_subst]
        apply KripkeSem.weaken
        · exact h₃
        · apply h₂
  case app _ _ t₁ _ _ _ _ _ ih₁ ih₂ =>
    conv in t₁.subst σ => rw [←Term.weaken_id (t := t₁[σ])]
    apply ih₁
    · exact h₂
    · exact Context.weaken_id
    · exact ih₂ h₂
  case pair => apply KripkeSem.pair <;> aesop
  case fst ih => exact (ih h₂).left
  case snd ih => exact (ih h₂).right
  case bool => exact StrongNormal.bool

theorem strong_normalization : Γ ⊢ t : T → StrongNormal t := by
  intro h
  apply KripkeSem.strong_normal
  rw [←Term.subst_id (t := t)]
  apply KripkeSem.fundamental
  · exact h
  · intro x; apply KripkeSem.var
