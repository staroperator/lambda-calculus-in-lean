import Lambda.SystemT.Operational

namespace SystemT

open Term in
@[aesop unsafe [constructors]]
inductive ParStep : Rel (Term Γ T) where
| var : ParStep #x #x
| lam : ParStep t t' → ParStep (λ' t) (λ' t')
| app : ParStep t₁ t₁' → ParStep t₂ t₂' → ParStep (t₁ ⬝ t₂) (t₁' ⬝ t₂')
| beta : ParStep t₁ t₁' → ParStep t₂ t₂' → ParStep (λ' t₁ ⬝ t₂) (t₁'[↦ t₂']ˢ)
| true : ParStep true true
| false : ParStep false false
| ite : ParStep t₁ t₁' → ParStep t₂ t₂' → ParStep t₃ t₃' →
  ParStep (ite t₁ t₂ t₃) (ite t₁' t₂' t₃')
| ite_true : ParStep t₂ t₂' → ParStep (Term.ite true t₂ t₃) t₂'
| ite_false : ParStep t₃ t₃' → ParStep (Term.ite false t₂ t₃) t₃'
| zero : ParStep zero zero
| succ : ParStep t t' → ParStep (succ t) (succ t')
| recn : ParStep t₁ t₁' → ParStep t₂ t₂' → ParStep t₃ t₃' →
  ParStep (recn t₁ t₂ t₃) (recn t₁' t₂' t₃')
| recn_zero : ParStep t₂ t₂' → ParStep (recn zero t₂ t₃) t₂'
| recn_succ : ParStep t₁ t₁' → ParStep t₂ t₂' → ParStep t₃ t₃' → 
  ParStep (recn (succ t₁) t₂ t₃) (t₃' ⬝ t₁' ⬝ (recn t₁' t₂' t₃'))
-- | recn_succ : ParStep t₁ (succ t₁') → ParStep t₂ t₂' → ParStep t₃ t₃' →
--   ParStep (recn t₁ t₂ t₃) (t₃' ⬝ t₁' ⬝ (recn t₁' t₂' t₃'))
| pair : ParStep t₁ t₁' → ParStep t₂ t₂' → ParStep ⟪t₁, t₂⟫ ⟪t₁', t₂'⟫
| fst : ParStep t t' → ParStep t.fst t'.fst
| snd : ParStep t t' → ParStep t.snd t'.snd
| sigma₁ : ParStep t₁ t₁' → ParStep ⟪t₁, t₂⟫.fst t₁'
| sigma₂ : ParStep t₂ t₂' → ParStep ⟪t₁, t₂⟫.snd t₂'

infix:55 " ⟹ " => ParStep

@[aesop safe] lemma ParStep.refl : t ⟹ t := by
  induction t <;> constructor <;> assumption

lemma ParStep.of_step : t ⟶ t' → t ⟹ t' := by
  intro h
  induction h <;> aesop

lemma ParStep.multi_step : t ⟹ t' → t ⟶* t' := by
  intro h
  induction h with
  | var | true | false | zero => apply Rel.Multi.refl
  | lam _ ih | succ _ ih | fst _ ih | snd _ ih =>
    apply Rel.Multi.congr ih; aesop
  | app _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ =>
    apply Rel.Multi.congr₂ ih₁ ih₂ <;> aesop
  | ite _ _ _ ih₁ ih₂ ih₃ | recn _ _ _ ih₁ ih₂ ih₃ =>
    apply Rel.Multi.congr₃ ih₁ ih₂ ih₃ <;> aesop
  | beta _ _ ih₁ ih₂ =>
    apply Rel.Multi.trans
    · apply Rel.Multi.congr₂ (Rel.Multi.congr ih₁ _) <;> aesop
    · exact Rel.Multi.step Step.beta Rel.Multi.refl
  | recn_succ _ _ _ ih₁ ih₂ ih₃ =>
    apply Rel.Multi.trans
    · apply Rel.Multi.congr₃ ih₁ ih₂ ih₃ <;> aesop
    · apply Rel.Multi.step
      · exact Step.recn_succ
      · exact Rel.Multi.refl
  | sigma₁ | sigma₂ | ite_true | ite_false | recn_zero =>
    constructor <;> aesop

theorem ParStep.weaken {ρ : Weaken n m} :
  t ⟹ t' → t[ρ]ʷ ⟹ t'[ρ]ʷ := by
  intro h
  induction h generalizing m
  case beta ih₁ ih₂ =>
    simp [substitution_weaken]
    apply ParStep.beta <;> aesop
  all_goals aesop

theorem ParStep.strong_substitutivity {σ₁ σ₂ : Subst Γ Δ} :
  t ⟹ t' → (∀ {T} (x : T ∈' Γ), σ₁ x ⟹ σ₂ x) →
  t[σ₁]ˢ ⟹ t'[σ₂]ˢ := by
  intros h₁ h₂
  induction h₁ generalizing Δ
  case lam _ ih =>
    simp; constructor; apply ih; intro _ x
    cases x <;> simp [Subst.lift]
    · constructor
    · apply ParStep.weaken
      apply h₂
  case beta ih₁ ih₂ =>
    simp; conv => arg 2; simp [substitution]
    constructor
    · apply ih₁
      intro _ x
      cases x <;> simp [Subst.lift]
      · constructor
      · apply ParStep.weaken
        apply h₂
    · apply ih₂ h₂
  all_goals aesop

theorem ParStep.strong_substitutivity_single :
  t₁ ⟹ t₁' → t₂ ⟹ t₂' → t₁[↦ t₂]ˢ ⟹ t₁'[↦ t₂']ˢ := by
  intros h₁ h₂
  apply ParStep.strong_substitutivity h₁
  intro _ x
  cases x <;> simp [Subst.single]
  · exact h₂
  · constructor

def Term.complete : Term Γ T → Term Γ T
| #x => #x
| λ' t => λ' t.complete
| (λ' t₁ ⬝ t₂) => (t₁.complete)[↦ t₂.complete]ˢ
| t₁ ⬝ t₂ => t₁.complete ⬝ t₂.complete
| true => true
| false => false
| ite true t₂ _ => t₂.complete
| ite false _ t₃ => t₃.complete
| ite t₁ t₂ t₃ => ite t₁.complete t₂.complete t₃.complete
| zero => zero
| succ t => succ t.complete
| recn zero t₁ t₂ => t₁.complete
| recn (succ t₁) t₂ t₃ =>
  t₃.complete ⬝ t₁.complete ⬝ (recn t₁.complete t₂.complete t₃.complete)
| recn t₁ t₂ t₃ => recn t₁.complete t₂.complete t₃.complete
| ⟪t₁, t₂⟫ => ⟪t₁.complete, t₂.complete⟫
| fst ⟪t₁, _⟫ => t₁.complete
| fst t => fst t.complete
| snd ⟪_, t₂⟫ => t₂.complete
| snd t => snd t.complete

theorem ParStep.complete : t ⟹ t.complete := by
  induction t
  case app t₁ _ ih₁ _ =>
    cases t₁ <;> simp [Term.complete]
    case lam => cases ih₁; aesop
    all_goals aesop
  case ite t₁ _ _ ih₁ _ _ =>
    cases t₁ <;> simp [Term.complete]
    case true | false => cases ih₁; aesop
    all_goals aesop
  case recn t₁ _ _ ih₁ _ _ =>
    cases t₁ <;> simp [Term.complete]
    case zero | succ => cases ih₁; aesop
    all_goals aesop
  case fst t ih =>
    cases t <;> simp [Term.complete]
    case pair => cases ih; aesop
    all_goals aesop
  case snd t ih =>
    cases t <;> simp [Term.complete]
    case pair => cases ih; aesop
    all_goals aesop
  all_goals simp [Term.complete]; aesop

theorem ParStep.of_complete : t ⟹ t' → t' ⟹ t.complete := by
  intro h
  induction h
  case app h₁ _ ih₁ _ =>
    cases h₁ <;> simp [Term.complete]
    case lam => cases ih₁; aesop
    all_goals aesop
  case beta =>
    simp [Term.complete]
    apply ParStep.strong_substitutivity_single <;> assumption
  case ite h₁ _ _ ih₁ _ _ =>
    cases h₁ <;> simp [Term.complete]
    case true | false => cases ih₁; aesop
    all_goals aesop
  case recn h₁ _ _ ih₁ _ _ =>
    cases h₁ <;> simp [Term.complete]
    case zero | succ => cases ih₁; aesop
    all_goals aesop
  case fst h ih | snd h ih =>
    cases h <;> simp [Term.complete]
    case pair => cases ih; aesop
    all_goals aesop
  all_goals simp [Term.complete]; aesop

theorem ParStep.diamond : (@ParStep Γ T).Diamond := by
  intros t t₁ t₂ h₁ h₂
  exists t.complete
  constructor <;> apply ParStep.of_complete <;> assumption

def ParReduce : Rel (Term Γ T) := ParStep.Multi
infix:55 " ⟹* " => ParReduce

theorem ParReduce.iff_multi_step :
  t ⟹* t' ↔ t ⟶* t' := by
  constructor
  · intro h; induction h
    · constructor
    · apply Rel.Multi.trans
      · apply ParStep.multi_step; assumption
      · assumption
  · intro h; induction h
    · constructor
    · constructor
      · apply ParStep.of_step; assumption
      · assumption

theorem church_rosser : (@Reduce Γ T).Diamond := by
  unfold Rel.Diamond
  simp [←ParReduce.iff_multi_step]
  apply Rel.Multi.diamond
  exact ParStep.diamond

end SystemT
