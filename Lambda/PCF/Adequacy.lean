import Lambda.PCF.Denotational

namespace PCF

def R : (T : Ty) → Term ∅ T → ⟦T⟧ᵀ → Prop
| TBool, t, d =>
  (d = some true → t ⟶* Term.true) ∧
  (d = some false → t ⟶* Term.false)
| TNat, t, d =>
  ∀ n, d = some n → t ⟶* Term.nat n
| T₁ ⇒ T₂, t, d =>
  ∀ t' d', R T₁ t' d' → R T₂ (t ⬝ t') (d d')
| T₁ * T₂, t, ⟨d₁, d₂⟩ =>
  R T₁ (Term.fst t) d₁ ∧ R T₂ (Term.snd t) d₂

lemma R.bot : R T t ⊥ := by
  induction T with
  | bool => constructor <;> intro <;> contradiction
  | nat => intro _ _; contradiction
  | fn T₁ T₂ _ ih₂ =>
    intro t' d' _; exact ih₂
  | prod T₁ T₂ ih₁ ih₂ =>
    exact ⟨ih₁, ih₂⟩

theorem R.le {d d' : ⟦T⟧ᵀ} :
  d' ≤ d → R T t d → R T t d' := by
  intro h₁ h₂
  induction T with
  | bool =>
    cases' d with b <;> cases' d' with b' <;>
      cases h₁ <;> try assumption
    exact bot
  | nat =>
    cases' d with n <;> cases' d' with n' <;>
      cases h₁ <;> try assumption
    exact bot
  | fn T₁ T₂ _ ih₂ =>
    intro t' d₁ h₃
    apply ih₂
    · apply h₁
    · apply h₂; exact h₃
  | prod T₁ T₂ ih₁ ih₂ =>
    cases' d with d₁ d₂
    cases' d' with d₁' d₂'
    cases' h₁ with h₁ h₁'
    constructor
    · exact ih₁ h₁ h₂.left
    · exact ih₂ h₁' h₂.right

theorem R.sup {s : Set ⟦T⟧ᵀ} {hs : Directed' s} :
  (∀ x ∈ s, R T t x) → R T t (Dcpo.sSup s hs) := by
  intro h
  induction T with
  | bool | nat =>
    rcases Domain.Flat.directed_cases hs with h₁ | ⟨x, h₁⟩ | ⟨x, h₁⟩ <;>
      subst h₁ <;> simp [Dcpo.sSup_singleton, Dcpo.sSup_pair bot_le] <;>
      apply h <;> aesop
  | fn T₁ T₂ _ ih₂ =>
    intro t' d h₁
    apply ih₂
    intro _ ⟨f, h₂, h₃⟩
    subst h₃
    apply h _ h₂
    exact h₁
  | prod T₁ T₂ ih₁ ih₂ =>
    constructor
    · apply ih₁
      intro _ ⟨⟨d₁, d₂⟩, h₁, h₂⟩; subst h₂
      exact (h _ h₁).left
    · apply ih₂
      intro _ ⟨⟨d₁, d₂⟩, h₁, h₂⟩; subst h₂
      exact (h _ h₁).right

theorem R.inv_step {t t' : Term ∅ T} :
  t ⟶ t' → R T t' d → R T t d := by
  intro h₁ h₂
  induction T with
  | bool =>
    constructor <;> intro h₃ <;> apply Rel.Multi.step h₁
    · exact h₂.left h₃
    · exact h₂.right h₃
  | nat =>
    intro _ h₃; apply Rel.Multi.step h₁; exact h₂ _ h₃
  | fn T₁ T₂ _ ih₂ =>
    intro t' d' h₃
    apply ih₂ (Step.app₁ h₁)
    apply h₂
    · exact h₃
  | prod T₁ T₂ ih₁ ih₂ =>
    constructor
    · exact ih₁ (Step.fst h₁) h₂.left
    · exact ih₂ (Step.snd h₁) h₂.right

theorem R.inv_reduce {t t' : Term ∅ T} :
  t ⟶* t' → R T t' d → R T t d := by
  intro h₁ h₂
  induction h₁ with
  | refl => exact h₂
  | step h₁ _ ih => apply inv_step h₁; exact ih h₂

def Rsub (σ : Subst Γ ∅) (g : ⟦Γ⟧ᴳ) :=
  ∀ T (x : T ∈' Γ), R T (σ x) (Con.denot_get x g)

theorem R.fundamental :
  Rsub σ g → R T (t[σ]ˢ) (⟦t⟧ᵗ g) := by
  intro h
  induction t with simp [Term.denot]
  | var x => apply h
  | lam t ih =>
    intro t' d h₁'
    apply inv_step Step.beta
    simp [Term.subst_comp]
    apply ih
    intro _ x
    cases x with
    | fz => exact h₁'
    | fs x =>
      simp [Subst.comp, Subst.lift, Term.shift_subst_single, Con.denot_get]
      apply h
  | app t₁ t₂ ih₁ ih₂ =>
    apply ih₁ h
    exact ih₂ h
  | fix t ih =>
    apply sup
    intro _ ⟨n, h₁⟩; subst h₁
    induction' n with n ih'
    · exact bot
    · simp [Domain.iter]
      apply inv_step Step.fix₂
      apply ih h
      exact ih'
  | true | false =>
    constructor <;> intro h <;> cases h; constructor
  | ite t₁ t₂ t₃ ih₁ ih₂ ih₃ =>
    simp [Domain.ite]; split
    next h₁ =>
      apply (ih₁ h).left at h₁
      apply inv_reduce
      · apply Rel.Multi.congr h₁ Step.ite₁
      · apply inv_step Step.ite_true
        exact ih₂ h
    next h₁ =>
      apply (ih₁ h).right at h₁
      apply inv_reduce
      · apply Rel.Multi.congr h₁ Step.ite₁
      · apply inv_step Step.ite_false
        exact ih₃ h
    next => exact bot
  | nat n => intro _ h; cases h; constructor
  | succ t ih =>
    simp [Domain.succ]; split
    next h₁ =>
      apply ih h at h₁
      apply inv_reduce
      · apply Rel.Multi.congr h₁ Step.succ
      · apply inv_step Step.succ_nat
        intro _ h; cases h; constructor
    next => exact bot
  | pred t ih =>
    simp [Domain.pred]; split
    next h₁ =>
      apply ih h at h₁
      apply inv_reduce
      · apply Rel.Multi.congr h₁ Step.pred
      · apply inv_step Step.pred_zero
        intro _ h; cases h; constructor
    next h₁ =>
      apply ih h at h₁
      apply inv_reduce
      · apply Rel.Multi.congr h₁ Step.pred
      · apply inv_step Step.pred_succ
        intro _ h; cases h; constructor
    next => exact bot
  | isz t ih =>
    simp [Domain.isz]; split
    next h₁ =>
      apply ih h at h₁
      apply inv_reduce
      · apply Rel.Multi.congr h₁ Step.isz
      · apply inv_step Step.isz_zero
        constructor <;> intro h <;> cases h; constructor
    next h₁ =>
      apply ih h at h₁
      apply inv_reduce
      · apply Rel.Multi.congr h₁ Step.isz
      · apply inv_step Step.isz_succ
        constructor <;> intro h <;> cases h; constructor
    next => exact bot
  | pair t₁ t₂ ih₁ ih₂ =>
    constructor
    · apply inv_step Step.sigma₁; exact ih₁ h
    · apply inv_step Step.sigma₂; exact ih₂ h
  | fst t ih => exact (ih h).left
  | snd t ih => exact (ih h).right



theorem adequacy {v t : Term ∅ T} :
  Value v → ⟦t⟧ᵗ () = ⟦v⟧ᵗ () → t ⟶* v := by
  intro h₁ h₂
  have h₃ : R T t (⟦t⟧ᵗ ()) := by
    conv => arg 2; rw [←Term.subst_id (t := t)]
    apply R.fundamental
    intro _ x; cases x
  rw [h₂] at h₃
  cases v with simp [Value] at h₁
  | true => exact h₃.left rfl
  | false => exact h₃.right rfl
  | nat n => exact h₃ n rfl

lemma denot_value_le {v : Term ∅ T} :
  Value v → ⟦v⟧ᵗ () ≤ d → d = ⟦v⟧ᵗ () := by
  intro h₁ h₂
  cases v <;> simp [Value, Term.denot] at * <;>
    cases d <;> cases h₂ <;> rfl

theorem denot_le_implies_context_approx :
  ⟦t₁⟧ᵗ ≤ ⟦t₂⟧ᵗ → t₁ ≲ᶜ t₂ := by
  intro h₁ T C v h₂ h₃
  apply Reduce.denot_eq at h₃
  apply adequacy h₂
  apply denot_value_le h₂
  simp [←h₃, Context.denot_plug]
  apply ⟦C⟧ᶜ.2.mono
  exact h₁

theorem denot_eq_implies_context_equiv :
  ⟦t₁⟧ᵗ = ⟦t₂⟧ᵗ → t₁ ≈ᶜ t₂ := by
  intro h₁ T C v h₂
  constructor <;> apply denot_le_implies_context_approx <;> aesop

end PCF
