import Lambda.SystemT.Operational
import Mathlib.Data.Nat.Basic

namespace SystemT

def StrongNormal (t : Term Γ T) := Step.StrongNormal t
def StrongNormal' (k) (t : Term Γ T) := Step.StrongNormal' k t

def Term.stepRange : Term Γ T → List (Term Γ T)
| #_ | true | false | zero => []
| λ' t => t.stepRange.map (λ' .)
| t₁ ⬝ t₂ =>
  let l := t₁.stepRange.map (. ⬝ t₂) ++ t₂.stepRange.map (t₁ ⬝ .)
  match t₁ with
  | λ' t₁ => t₁[↦ t₂]ˢ :: l
  | _ => l
| ite t₁ t₂ t₃ =>
  let l := t₁.stepRange.map (ite . t₂ t₃) ++
    t₂.stepRange.map (ite t₁ . t₃) ++ t₃.stepRange.map (ite t₁ t₂ .)
  match t₁ with
  | true => t₂ :: l
  | false => t₃ :: l
  | _ => l
| succ t => t.stepRange.map (succ .)
| recn t₁ t₂ t₃ =>
  let l := t₁.stepRange.map (recn . t₂ t₃) ++
    t₂.stepRange.map (recn t₁ . t₃) ++ t₃.stepRange.map (recn t₁ t₂ .)
  match t₁ with
  | zero => t₂ :: l
  | succ t₁ => t₃ ⬝ t₁ ⬝ recn t₁ t₂ t₃ :: l
  | _ => l
| ⟪t₁, t₂⟫ => t₁.stepRange.map (⟪., t₂⟫) ++ t₂.stepRange.map (⟪t₁, .⟫)
| fst t =>
  let l := t.stepRange.map (fst .)
  match t with
  | ⟪t₁, _⟫ => t₁ :: l
  | _ => l
| snd t =>
  let l := t.stepRange.map (snd .)
  match t with
  | ⟪_, t₂⟫ => t₂ :: l
  | _ => l

lemma Step.finite : (@Step Γ T).Finite := by
  intro t
  exists t.stepRange
  intro t'
  induction t <;> rw [Term.stepRange] <;> (
    constructor
    · intro h; cases h <;> aesop
    · aesop)

lemma StrongNormal.strong_normal' :
  StrongNormal t → ∃ k, StrongNormal' k t := by
  apply Rel.StrongNormal.strong_normal'
  exact Step.finite

lemma StrongNormal.weaken : StrongNormal t → StrongNormal (t[ρ]ʷ) := by
  intro h; induction' h with t _ ih
  constructor; intros _ h
  rcases Step.inversion_weaken h with ⟨t', h₁, h₂⟩
  subst h₂
  apply ih; exact h₁

lemma StrongNormal.strengthen :
  StrongNormal (t[ρ]ʷ) → StrongNormal t := by
  intro h
  generalize h' : t[ρ]ʷ = t' at h
  induction' h with t _ ih generalizing t; subst h'
  constructor; intros _ h
  apply ih
  · apply Step.weaken; exact h
  · rfl

lemma StrongNormal.inversion_app :
  StrongNormal (t₁ ⬝ t₂) → StrongNormal t₁ := by
  intro h₁
  generalize h₂ : t₁ ⬝ t₂ = t at h₁
  induction' h₁ with _ _ ih generalizing t₁ t₂; subst h₂
  constructor; intros _ h
  apply ih
  · exact Step.app₁ h
  · rfl

lemma StrongNormal.inversion_fst :
  StrongNormal (Term.fst t) → StrongNormal t := by
  intro h₁
  generalize h₂ : Term.fst t = t' at h₁
  induction' h₁ with _ _ ih generalizing t; subst h₂
  constructor; intros _ h
  apply ih
  · exact Step.fst h
  · rfl

lemma StrongNormal.inversion_succ :
  StrongNormal (Term.succ t) → StrongNormal t := by
  intro h₁
  generalize h₂ : Term.succ t = t' at h₁
  induction' h₁ with _ _ ih generalizing t; subst h₂
  constructor; intros _ h
  apply ih
  · exact Step.succ h
  · rfl

lemma StrongNormal'.inversion_succ :
  StrongNormal' k (Term.succ t) → StrongNormal' k t := by
  intro h₁
  generalize h₂ : Term.succ t = t' at h₁
  induction' h₁ with _ _ _ ih generalizing t; subst h₂
  constructor; intros _ h
  apply ih
  · exact Step.succ h
  · rfl

lemma StrongNormal.succ :
  StrongNormal t → StrongNormal (Term.succ t) := by
  intro h₁
  induction' h₁ with _ _ ih
  constructor; intros _ h
  cases h
  apply ih
  assumption



def R : (T : Ty) → Term Γ T → Prop
| TBool, t | TNat, t => StrongNormal t
| T₁ ⇒ T₂, t => ∀ Δ (ρ : Γ ⊆ʷ Δ) t', R T₁ t' → R T₂ (t[ρ]ʷ ⬝ t')
| T₁ * T₂, t => R T₁ (Term.fst t) ∧ R T₂ (Term.snd t)

def Rsub (Δ : Con) (σ : Subst Γ Δ) : Prop :=
  ∀ {T} (x : T ∈' Γ), R T (σ x)

lemma R.weaken {t : Term Γ T} : R T t → R T (t[ρ]ʷ) := by
  intro h
  induction T generalizing Γ with simp [R] at *
  | bool | nat => exact StrongNormal.weaken h
  | fn T₁ T₂ _ _ =>
    intros Δ ρ t' h₁
    simp [Term.weaken_comp]
    apply h; exact h₁
  | prod T₁ T₂ ih₁ ih₂ =>
    constructor
    · apply ih₁ (t := Term.fst t); exact h.left
    · apply ih₂ (t := Term.snd t); exact h.right

lemma R.step {t : Term Γ T} : t ⟶ t' → R T t → R T t' := by
  intros h₁ h₂
  induction T generalizing Γ with simp [R] at *
  | bool | nat => exact Rel.StrongNormal.step h₁ h₂
  | fn T₁ T₂ _ ih₂ =>
    intros Δ ρ t'' h₃
    apply ih₂
    · exact Step.app₁ (Step.weaken h₁)
    · apply h₂; exact h₃
  | prod T₁ T₂ ih₁ ih₂ =>
    constructor
    · apply ih₁ (Step.fst h₁); exact h₂.left
    · apply ih₂ (Step.snd h₁); exact h₂.right

def R.Neutral : Term Γ T → Prop
| λ' _ | ⟪_, _⟫  => False
| _ => True

mutual
theorem R.strong_normal {t : Term Γ T} :
  R T t → StrongNormal t := by
  intro h
  match T with
  | TBool | TNat => exact h
  | T₁ ⇒ T₂ =>
    have h₁ : R (Γ := Γ,' T₁) T₂ (↑ₜt ⬝ #fz) := by
      apply h
      apply neutral_reducible
      · constructor
      · intro _ h'; cases h'
    apply strong_normal (T := T₂) at h₁
    apply StrongNormal.strengthen
    apply StrongNormal.inversion_app
    exact h₁
  | T₁ * T₂ =>
    apply StrongNormal.inversion_fst
    apply strong_normal
    exact h.left

theorem R.neutral_reducible {t : Term Γ T} :
  Neutral t → (∀ t', t ⟶ t' → R T t') → R T t := by
  intros h₁ h₂
  match T with
  | TBool | TNat => constructor; exact h₂
  | T₁ ⇒ T₂ =>
    intros Δ ρ t' h₃
    have h₄ := strong_normal h₃; induction' h₄ with t' _ ih
    apply neutral_reducible
    · constructor
    · intros t'' h₄
      generalize h₅ : t[ρ]ʷ = t₁ at h₄
      cases h₄ with
      | app₁ h₄ =>
        subst h₅
        apply Step.inversion_weaken at h₄
        rcases h₄ with ⟨t₁', h₄, h₅⟩; subst h₅
        apply h₂
        · exact h₄
        · exact h₃
      | app₂ h₄ =>
        subst h₅
        apply ih
        · exact h₄
        · exact step h₄ h₃
      | beta =>
        cases t <;> simp at h₅
        contradiction
  | T₁ * T₂ =>
    constructor
    · apply neutral_reducible
      · constructor
      · intros t' h₃
        cases h₃ with
        | fst h₃ => apply h₂ at h₃; exact h₃.left
        | sigma₁ => cases h₁
    · apply neutral_reducible
      · constructor
      · intros t' h₃
        cases h₃ with
        | snd h₃ => apply h₂ at h₃; exact h₃.right
        | sigma₂ => cases h₁
end

lemma R.var : R T #x := by
  apply neutral_reducible
  · constructor
  · intro _ h; cases h

lemma R.lam {t : Term _ T₂} :
  StrongNormal t →
  (∀ Δ (ρ : Γ ⊆ʷ Δ) (t' : Term Δ T₁), R T₁ t' → R T₂ (t[⇑ʷρ]ʷ[↦ t']ˢ)) →
  R (T₁ ⇒ T₂) (λ' t) := by
  intros h₁ h₂ Δ ρ t' h₃
  simp
  induction' h₁ with t _ ih₁
  induction' strong_normal h₃ with t' _ ih₂
  apply neutral_reducible
  · constructor
  · intros t'' h₄
    cases h₄ with
    | app₁ h₄ =>
      cases h₄ with | lam h₄ =>
      apply Step.inversion_weaken at h₄
      rcases h₄ with ⟨t', h₄, h₅⟩; subst h₅
      apply ih₁ _ h₄
      intros Δ ρ t'' h
      apply step
      · apply Step.subst; apply Step.weaken; exact h₄
      · apply h₂; assumption
    | app₂ h₄ =>
      apply ih₂ _ h₄
      · exact step h₄ h₃
      · intros t'' h₅ h₆
        apply step
        · exact Step.app₂ h₄
        · apply ih₁ <;> assumption
    | beta => apply h₂; assumption

lemma R.pair :
  R T₁ t₁ → R T₂ t₂ → R (T₁ * T₂) ⟪t₁, t₂⟫ := by
  intros h₁ h₂
  induction' strong_normal h₁ with t₁ _ ih₁
  induction' strong_normal h₂ with t₂ _ ih₂
  constructor
  · apply neutral_reducible
    · constructor
    · intros t' h
      cases h with
      | sigma₁ => exact h₁
      | fst h =>
        cases h with
        | pair₁ h =>
          apply And.left; apply ih₁
          · exact h
          · exact step h h₁
        | pair₂ h =>
          apply And.left; apply ih₂
          · exact h
          · exact step h h₂
          · intros; apply step
            · exact Step.pair₂ h
            · apply ih₁ <;> assumption
  · apply neutral_reducible
    · constructor
    · intros t' h
      cases h with
      | sigma₂ => exact h₂
      | snd h =>
        cases h with
        | pair₁ h =>
          apply And.right; apply ih₁
          · exact h
          · exact step h h₁
        | pair₂ h =>
          apply And.right; apply ih₂
          · exact h
          · exact step h h₂
          · intros; apply step
            · exact Step.pair₂ h
            · apply ih₁ <;> assumption

lemma R.ite :
  StrongNormal t₁ → R T t₂ → R T t₃ → R T (Term.ite t₁ t₂ t₃) := by
  intros h₁ h₂ h₃
  induction' h₁ with t₁ _ ih₁
  induction' strong_normal h₂ with t₂ _ ih₂
  induction' strong_normal h₃ with t₃ _ ih₃
  apply neutral_reducible
  · constructor
  · intros t' h
    cases h with
    | ite₁ h => apply ih₁; exact h
    | ite₂ h =>
      apply ih₂
      · exact h
      · exact step h h₂
      · intros _ h'
        apply step (Step.ite₂ h)
        apply ih₁; exact h'
    | ite₃ h =>
      apply ih₃
      · exact h
      · exact step h h₃
      · intros _ h₁' h₂' _
        apply step (Step.ite₃ h)
        apply ih₂
        · exact h₁'
        · exact h₂'
        · intros _ h₄'
          apply step (Step.ite₂ h₁')
          apply ih₁; exact h₄'
      · intros _ h'
        apply step (Step.ite₃ h)
        apply ih₁; exact h'
    | ite_true => exact h₂
    | ite_false => exact h₃

lemma R.app : R (T₁ ⇒ T₂) t₁ → R T₁ t₂ → R T₂ (t₁ ⬝ t₂) := by
  intros h₁ h₂
  have h := h₁ _ idʷ _ h₂
  simp [Term.weaken_id] at h
  exact h

lemma R.recn :
  Step.StrongNormal' k t₁ → R T t₂ → R _ t₃ →
  R T (Term.recn t₁ t₂ t₃) := by
  intros h₁ h₂ h₃
  induction' k using Nat.strong_induction_on with k ih₁ generalizing t₁
  induction' t₁ using Term.strong_induction with t₁ ih generalizing t₂ t₃
  induction' strong_normal h₂ with t₂ h₂' ih₂
  induction' strong_normal h₃ with t₃ h₃' ih₃
  apply neutral_reducible
  · constructor
  · intros t' h
    cases h with
    | recn₁ h =>
      rcases Rel.StrongNormal'.step h h₁ with ⟨k', h₁', h₂'⟩
      apply ih₁ _ h₁'; exact h₂'
    | recn₂ h =>
      apply ih₂
      · exact h
      · exact step h h₂
      · intros; apply step (Step.recn₂ h); apply ih₁ <;> assumption
    | recn₃ h =>
      apply ih₃
      · exact h
      · exact step h h₃
      · intros _ h' _ _
        apply step (Step.recn₃ h)
        apply ih₂
        · assumption
        · assumption
        · intros; apply step (Step.recn₂ h'); apply ih₁ <;> assumption
      · intros
        apply step (Step.recn₃ h)
        aesop
    | recn_zero => exact h₂
    | @recn_succ _ _ t₁ =>
      have h₁'' : R TNat t₁ := by
        apply StrongNormal.inversion_succ
        apply Rel.StrongNormal'.strong_normal
        exact h₁
      have h₂'' : R T (Term.recn t₁ t₂ t₃) := by
        apply ih
        · simp [Term.rank]
        · exact h₂
        · exact h₃
        · exact ih₁
        · exact StrongNormal'.inversion_succ h₁
      exact R.app (R.app h₃ h₁'') h₂''

theorem R.fundamental {σ : Subst Γ Δ} :
  Rsub Δ σ → R T (t[σ]ˢ) := by
  intro h
  induction t generalizing Δ with simp
  | var => apply h
  | @lam Γ T₁ T₂ t ih =>
    apply lam
    · apply strong_normal
      apply ih (Δ := Δ,' T₁)
      intro _ x; cases x with simp [Subst.lift]
      | fz => apply var
      | fs x => apply weaken; apply h
    · intros Θ ρ t' h₃
      simp [Term.subst_comp_weaken, Term.subst_comp]
      apply ih
      intro _ x; cases x with
      | fz => simp [Subst.comp, Subst.single]; exact h₃
      | fs x =>
        simp [Subst.comp, Subst.lift]
        rw [Weaken.lift_of_subst, Term.shift_subst_lift,
          Term.shift_subst_single, ←Term.weaken_eq_subst]
        apply weaken; apply h
  | app t₁ _ ih₁ ih₂ =>
    conv in t₁[σ]ˢ => rw [←Term.weaken_id (t := t₁[σ]ˢ)]
    apply ih₁ h
    apply ih₂ h
  | true | false => constructor; intro _ h; cases h
  | ite t₁ t₂ t₃ ih₁ ih₂ ih₃ =>
    apply ite
    · apply strong_normal; exact ih₁ h
    · exact ih₂ h
    · exact ih₃ h
  | zero => constructor; intro _ h; cases h
  | succ t ih => exact StrongNormal.succ (ih h)
  | recn t₁ t₂ t₃ ih₁ ih₂ ih₃ =>
    rcases StrongNormal.strong_normal' (ih₁ h) with ⟨k, h₁⟩
    apply recn
    · exact h₁
    · exact ih₂ h
    · exact ih₃ h
  | pair => apply pair <;> aesop
  | fst t ih => exact (ih h).left
  | snd t ih => exact (ih h).right

theorem strong_normalization (t : Term Γ T) : StrongNormal t := by
  apply R.strong_normal
  rw [←Term.subst_id (t := t)]
  apply R.fundamental
  intro _ x
  apply R.var

theorem canonicity_bool {t : Term ∅ TBool} :
  t ⟶* Term.true ∨ t ⟶* Term.false := by
  have h := strong_normalization t
  apply Rel.StrongNormal.weak_normal at h
  rcases h with ⟨t', h, h'⟩
  apply canonical_form_bool at h'
  aesop

theorem canonicity_nat {t : Term ∅ TNat} :
  ∃ n, t ⟶* Term.ofNat n := by
  have h := strong_normalization t
  apply Rel.StrongNormal.weak_normal at h
  rcases h with ⟨t', h, h'⟩
  apply canonical_form_nat at h'
  rcases h' with ⟨n, h'⟩
  exists n
  aesop

end SystemT
