import Lambda.STLC.Extrinsic.Typing

inductive Step : Term n → Term n → Prop where
| lam : Step t t' → Step (λ' T t) (λ' T t')
| app₁ : Step t₁ t₁' → Step (t₁ ⬝ t₂) (t₁' ⬝ t₂)
| app₂ : Step t₂ t₂' → Step (t₁ ⬝ t₂) (t₁ ⬝ t₂')
| pair₁ : Step t₁ t₁' → Step ⟪t₁, t₂⟫ ⟪t₁', t₂⟫
| pair₂ : Step t₂ t₂' → Step ⟪t₁, t₂⟫ ⟪t₁, t₂'⟫
| fst : Step t₁ t₂ → Step t₁.fst t₂.fst
| snd : Step t₁ t₂ → Step t₁.snd t₂.snd
| beta : Step (λ' T t₁ ⬝ t₂) (t₁[↦ t₂])
| sigma₁ : Step ⟪t₁, t₂⟫.fst t₁
| sigma₂ : Step ⟪t₁, t₂⟫.snd t₂

infix:55 " ⟶ " => Step

theorem Step.subject_reduction :
  Γ ⊢ t : T → t ⟶ t' → Γ ⊢ t' : T := by
  intros h₁ h₂
  induction h₂ generalizing T
  case beta =>
    cases h₁
    case app h₁ h₂ =>
    cases h₂
    apply Typing.cut_single <;> assumption
  case sigma₁ =>
    cases h₁
    case fst h₁ =>
    cases h₁
    assumption
  case sigma₂ =>
    cases h₁
    case snd h₁ =>
    cases h₁
    assumption
  all_goals
    cases h₁; constructor <;> aesop

lemma Step.weaken {ρ : Weaken n m} :
  t ⟶ t' → t[ρ]ʷ ⟶ t'[ρ]ʷ := by
  intro h
  induction h generalizing m <;> simp
  case beta =>
    rw [substitution_weaken]
    constructor
  all_goals constructor <;> aesop

lemma Step.inversion_weaken {ρ : Weaken n m} :
  t[ρ]ʷ ⟶ t' → ∃ t'', t ⟶ t'' ∧ t' = t''[ρ]ʷ := by
  intro h
  generalize h₁ : t[ρ]ʷ = t₁ at h
  induction h generalizing n t <;>
    cases t <;> simp at h₁
  case lam | app₁ | app₂ | pair₁ | pair₂ =>
    rcases h₁ with ⟨h₁, h₂⟩
    subst h₁ h₂
    rename _ => ih
    rcases ih rfl with ⟨_, h₁, h₂⟩
    subst h₂
    first
    | exact ⟨_, ⟨Step.lam h₁, rfl⟩⟩
    | exact ⟨_, ⟨Step.app₁ h₁, rfl⟩⟩
    | exact ⟨_, ⟨Step.app₂ h₁, rfl⟩⟩
    | exact ⟨_, ⟨Step.pair₁ h₁, rfl⟩⟩
    | exact ⟨_, ⟨Step.pair₂ h₁, rfl⟩⟩
  case fst | snd =>
    subst h₁
    rename _ => ih
    rcases ih rfl with ⟨_, h₁, h₂⟩
    subst h₂
    first
    | exact ⟨_, ⟨Step.fst h₁, rfl⟩⟩
    | exact ⟨_, ⟨Step.snd h₁, rfl⟩⟩
  case beta t _ =>
    rcases h₁ with ⟨h₁, h₂⟩
    rcases t <;> simp at h₁
    rcases h₁ with ⟨h₁, h₃⟩
    subst h₁ h₂ h₃
    simp [←substitution_weaken]
    exact ⟨_, ⟨Step.beta, rfl⟩⟩
  case sigma₁ t | sigma₂ t =>
    rcases t <;> simp at h₁
    rcases h₁ with ⟨h₁, h₂⟩
    subst h₁ h₂
    exact ⟨_, ⟨by constructor, rfl⟩⟩

lemma Step.subst {σ : Subst n m} : t ⟶ t' → t[σ] ⟶ t'[σ] := by
  intro h
  induction h generalizing m <;> simp
  case beta =>
    rw [substitution]
    constructor
  all_goals constructor <;> aesop



inductive MultiStep : Term n → Term n → Prop where
| refl : MultiStep t t
| step : t₁ ⟶ t₂ → MultiStep t₂ t₃ → MultiStep t₁ t₃

infix:55 " ⟶* " => MultiStep

theorem MultiStep.subject_reduction :
  Γ ⊢ t : T → t ⟶* t' → Γ ⊢ t' : T := by
  intros h₁ h₂
  induction h₂
  case refl => assumption
  case step h₂ _ ih =>
    apply ih
    apply Step.subject_reduction <;> assumption

lemma MultiStep.trans : t₁ ⟶* t₂ → t₂ ⟶* t₃ → t₁ ⟶* t₃ := by
  intros h₁ h₂
  induction h₁
  · assumption
  · constructor <;> aesop

lemma MultiStep.congr_lam : t ⟶* t' → λ' T t ⟶* λ' T t' := by
  intro h
  induction h
  · constructor
  · constructor
    · constructor; assumption
    · assumption

lemma MultiStep.congr_app : t₁ ⟶* t₁' → t₂ ⟶* t₂' → (t₁ ⬝ t₂ ⟶* t₁' ⬝ t₂') := by
  intros h₁ h₂
  apply trans (t₂ := t₁' ⬝ t₂)
  · induction h₁
    · constructor
    · constructor
      · apply Step.app₁; assumption
      · aesop
  · induction h₂
    · constructor
    · constructor
      · apply Step.app₂; assumption
      · aesop

lemma MultiStep.congr_pair : t₁ ⟶* t₁' → t₂ ⟶* t₂' → ⟪t₁, t₂⟫ ⟶* ⟪t₁', t₂'⟫ := by
  intros h₁ h₂
  apply trans (t₂ := ⟪t₁', t₂⟫)
  · induction h₁
    · constructor
    · constructor
      · apply Step.pair₁; assumption
      · aesop
  · induction h₂
    · constructor
    · constructor
      · apply Step.pair₂; assumption
      · aesop
  
lemma MultiStep.congr_fst : t ⟶* t' → t.fst ⟶* t'.fst := by
  intro h
  induction h
  · constructor
  · constructor
    · constructor; assumption
    · assumption

lemma MultiStep.congr_snd : t ⟶* t' → t.snd ⟶* t'.snd := by
  intro h
  induction h
  · constructor
  · constructor
    · constructor; assumption
    · assumption



inductive ParStep : Term n → Term n → Prop where
| var : ParStep #x #x
| lam : ParStep t t' → ParStep (λ' T t) (λ' T t')
| app : ParStep t₁ t₁' → ParStep t₂ t₂' → ParStep (t₁ ⬝ t₂) (t₁' ⬝ t₂')
| pair : ParStep t₁ t₁' → ParStep t₂ t₂' → ParStep ⟪t₁, t₂⟫ ⟪t₁', t₂'⟫
| fst : ParStep t t' → ParStep t.fst t'.fst
| snd : ParStep t t' → ParStep t.snd t'.snd
| beta : ParStep t₁ t₁' → ParStep t₂ t₂' → ParStep (λ' T t₁ ⬝ t₂) (t₁'[↦ t₂'])
| sigma₁ : ParStep t₁ t₁' → ParStep ⟪t₁, t₂⟫.fst t₁'
| sigma₂ : ParStep t₂ t₂' → ParStep ⟪t₁, t₂⟫.snd t₂'
| bool : ParStep (Term.bool b) (Term.bool b)

infix:55 " ⟹ " => ParStep

lemma ParStep.refl : t ⟹ t := by
  induction t <;> constructor <;> assumption

inductive MultiParStep : Term n → Term n → Prop where
| refl : MultiParStep t t
| step : t₁ ⟹ t₂ → MultiParStep t₂ t₃ → MultiParStep t₁ t₃

infix:55 " ⟹* " => MultiParStep

lemma Step.par_step : t ⟶ t' → t ⟹ t' := by
  intro h
  induction h <;> constructor <;> first | exact ParStep.refl | assumption

lemma ParStep.multi_step : t ⟹ t' → t ⟶* t' := by
  intro h
  induction h
  case var => constructor
  case lam => apply MultiStep.congr_lam; assumption
  case app => apply MultiStep.congr_app <;> assumption
  case pair => apply MultiStep.congr_pair <;> assumption
  case fst => apply MultiStep.congr_fst; assumption
  case snd => apply MultiStep.congr_snd; assumption
  case beta =>
    apply MultiStep.trans
    · apply MultiStep.congr_app
      · apply MultiStep.congr_lam; assumption
      · assumption
    · constructor
      · apply Step.beta
      · constructor
  case sigma₁ =>
    apply MultiStep.trans
    · apply MultiStep.congr_fst
      apply MultiStep.congr_pair
      · assumption
      · apply MultiStep.refl
    · constructor
      · apply Step.sigma₁
      · constructor
  case sigma₂ =>
    apply MultiStep.trans
    · apply MultiStep.congr_snd
      apply MultiStep.congr_pair
      · apply MultiStep.refl
      · assumption
    · constructor
      · apply Step.sigma₂
      · constructor
  case bool => constructor

lemma MultiParStep.iff_multi_step : t ⟹* t' ↔ t ⟶* t' := by
  constructor
  · intro h
    induction h
    · constructor
    · apply MultiStep.trans
      · apply ParStep.multi_step; assumption
      · assumption
  · intro h
    induction h
    · constructor
    · constructor
      · apply Step.par_step; assumption
      · assumption

theorem ParStep.weaken {ρ : Weaken n m} :
  t ⟹ t' → t[ρ]ʷ ⟹ t'[ρ]ʷ := by
  intro h
  induction h generalizing m
  case beta ih₁ ih₂ =>
    simp [substitution_weaken]
    apply ParStep.beta <;> apply_assumption
  all_goals
    simp; constructor <;> aesop

theorem ParStep.strong_substitutivity {σ₁ σ₂ : Subst n m} :
  t ⟹ t' → (∀ x, σ₁ x ⟹ σ₂ x) → t[σ₁] ⟹ t'[σ₂] := by
  intros h₁ h₂
  induction h₁ generalizing m
  case lam _ ih =>
    simp
    constructor
    apply ih
    intro x
    cases x <;> simp [Subst.lift]
    · constructor
    · apply ParStep.weaken
      apply h₂
  case beta ih₁ ih₂ =>
    simp
    conv =>
      arg 2
      simp [substitution]
    constructor
    · apply ih₁
      intro x
      cases x <;> simp [Subst.lift]
      · constructor
      · apply ParStep.weaken
        apply h₂
    · apply ih₂ h₂
  all_goals
    simp; (try constructor) <;> aesop

theorem ParStep.strong_substitutivity_single :
  t₁ ⟹ t₁' → t₂ ⟹ t₂' → t₁[↦ t₂] ⟹ t₁'[↦ t₂'] := by
  intros h₁ h₂
  apply ParStep.strong_substitutivity h₁
  intro x
  cases x <;> simp [Subst.single]
  · exact h₂
  · constructor

theorem ParStep.diamond :
  t ⟹ t₁ → t ⟹ t₂ → ∃ t', t₁ ⟹ t' ∧ t₂ ⟹ t' := by
  intros h₁ h₂
  induction t with
  | var x => cases h₁; cases h₂; exists #x; repeat constructor
  | lam T t ih =>
    cases h₁ with | @lam _ _ t₁ _ h₁ =>
    cases h₂ with | @lam _ _ t₂ _ h₂ =>
    rcases ih h₁ h₂ with ⟨t', h₃, h₄⟩
    exists λ' T t'
    (repeat' constructor) <;> assumption
  | app t t' ih₁ ih₂ =>
    cases h₁ with
    | @app _ _ t₁ _ t₁' h₁ h₁' =>
      cases h₂ with
      | @app _ _ t₂ _ t₂' h₂ h₂' =>
        rcases ih₁ h₁ h₂ with ⟨t₃, h₃, h₄⟩
        rcases ih₂ h₁' h₂' with ⟨t₃', h₅, h₆⟩
        exists t₃ ⬝ t₃'
        (repeat' constructor) <;> assumption
      | @beta _ t t₂ _ t₂' T h₂ h₂' =>
        cases h₁ with | @lam _ _ t₁ _ h₁ =>
        rcases ih₁ (ParStep.lam h₁) (ParStep.lam h₂) with ⟨t₃, h₃, h₄⟩
        cases h₃ with | @lam _ _ t₃ _ h₃ =>
        cases h₄ with | @lam _ _ _ _ h₄ =>
        rcases ih₂ h₁' h₂' with ⟨t₃', h₅, h₆⟩
        exists t₃[↦ t₃']
        constructor
        · constructor <;> assumption
        · apply ParStep.strong_substitutivity_single <;> assumption
    | @beta _ t t₁ _ t₁' T h₁ h₁' =>
      cases h₂ with
      | @app _ _ t₂ _ t₂' h₂ h₂' =>
        cases h₂ with | @lam _ _ t₂ _ h₂ =>
        rcases ih₁ (ParStep.lam h₁) (ParStep.lam h₂) with ⟨t₃, h₃, h₄⟩
        cases h₃ with | @lam _ _ t₃ _ h₃ =>
        cases h₄ with | @lam _ _ _ _ h₄ =>
        rcases ih₂ h₁' h₂' with ⟨t₃', h₅, h₆⟩
        exists t₃[↦ t₃']
        constructor
        · apply ParStep.strong_substitutivity_single <;> assumption
        · constructor <;> assumption
      | @beta _ _ t₂ _ t₂' T h₂ h₂' =>
        rcases ih₁ (ParStep.lam h₁) (ParStep.lam h₂) with ⟨t₃, h₃, h₄⟩
        cases h₃ with | @lam _ _ t₃ _ h₃ =>
        cases h₄ with | @lam _ _ t₄ _ h₄ =>
        rcases ih₂ h₁' h₂' with ⟨t₃', h₅, h₆⟩
        exists t₃[↦ t₃']
        constructor <;> apply ParStep.strong_substitutivity_single <;> assumption
  | pair t t' ih₁ ih₂ =>
    cases h₁ with | @pair _ _ t₁ _ t₁' h₁ h₁' =>
    cases h₂ with | @pair _ _ t₂ _ t₂' h₂ h₂' =>
    rcases ih₁ h₁ h₂ with ⟨t₃, h₃, h₄⟩
    rcases ih₂ h₁' h₂' with ⟨t₃', h₅, h₆⟩
    exists ⟪t₃, t₃'⟫
    (repeat' constructor) <;> assumption
  | fst t ih =>
    cases h₁ with
    | @fst _ _ t₁ h₁ =>
      cases h₂ with
      | @fst _ _ t₂ h₂ =>
        rcases ih h₁ h₂ with ⟨t', h₃, h₄⟩
        exists t'.fst
        constructor <;> constructor <;> assumption
      | @sigma₁ _ t t₂ t' h₂ =>
        cases h₁ with | @pair _ _ t₁ _ t₁' h₁ h₁' =>
        rcases ih (ParStep.pair h₁ h₁') (ParStep.pair h₂ ParStep.refl) with ⟨t₃, h₃, h₄⟩
        cases h₃ with | @pair _ _ t₃ _ t₃' h₃ h₃' =>
        cases h₄ with | @pair _ _ _ _ _ h₄ h₄' =>
        exists t₃
        (repeat' constructor) <;> assumption
    | @sigma₁ _ t t₁ t' h₁ =>
      cases h₂ with
      | @fst _ _ t₂ h₂ =>
        cases h₂ with | @pair _ _ t₂ _ t₂' h₂ h₂' =>
        rcases ih (ParStep.pair h₁ ParStep.refl) (ParStep.pair h₂ h₂') with ⟨t₃, h₃, h₄⟩
        cases h₃ with | @pair _ _ t₃ _ t₃' h₃ h₃' =>
        cases h₄ with | @pair _ _ _ _ _ h₄ h₄' =>
        exists t₃
        (repeat' constructor) <;> assumption
      | @sigma₁ _ _ t₂ _ h₂ =>
        rcases ih (ParStep.pair h₁ ParStep.refl) (ParStep.pair h₂ ParStep.refl) with ⟨t₃, h₃, h₄⟩
        cases h₃ with | @pair _ _ t₃ _ t₃' h₃ h₃' =>
        cases h₄ with | @pair _ _ _ _ _ h₄ h₄' =>
        exists t₃
  | snd t ih =>
    cases h₁ with
    | @snd _ _ t₁ h₁ =>
      cases h₂ with
      | @snd _ _ t₂ h₂ =>
        rcases ih h₁ h₂ with ⟨t', h₃, h₄⟩
        exists t'.snd
        constructor <;> constructor <;> assumption
      | @sigma₂ _ t t₂ t' h₂ =>
        cases h₁ with | @pair _ _ t₁ _ t₁' h₁ h₁' =>
        rcases ih (ParStep.pair h₁ h₁') (ParStep.pair ParStep.refl h₂) with ⟨t₃, h₃, h₄⟩
        cases h₃ with | @pair _ _ t₃ _ t₃' h₃ h₃' =>
        cases h₄ with | @pair _ _ _ _ _ h₄ h₄' =>
        exists t₃'
        (repeat' constructor) <;> assumption
    | @sigma₂ _ t t₁ t' h₁ =>
      cases h₂ with
      | @snd _ _ t₂ h₂ =>
        cases h₂ with | @pair _ _ t₂ _ t₂' h₂ h₂' =>
        rcases ih (ParStep.pair ParStep.refl h₁) (ParStep.pair h₂ h₂') with ⟨t₃, h₃, h₄⟩
        cases h₃ with | @pair _ _ t₃ _ t₃' h₃ h₃' =>
        cases h₄ with | @pair _ _ _ _ _ h₄ h₄' =>
        exists t₃'
        (repeat' constructor) <;> assumption
      | @sigma₂ _ _ t₂ _ h₂ =>
        rcases ih (ParStep.pair ParStep.refl h₁) (ParStep.pair ParStep.refl h₂) with ⟨t₃, h₃, h₄⟩
        cases h₃ with | @pair _ _ t₃ _ t₃' h₃ h₃' =>
        cases h₄ with | @pair _ _ _ _ _ h₄ h₄' =>
        exists t₃'
  | bool b => cases h₁; cases h₂; exists Term.bool b; repeat' constructor

lemma MultiParStep.stripe :
  t ⟹ t₁ → t ⟹* t₂ → ∃ t', t₁ ⟹* t' ∧ t₂ ⟹ t' := by
  intros h₁ h₂
  induction h₂ generalizing t₁ with
  | refl => exists t₁; constructor <;> first | constructor | assumption
  | step h₂ _ ih =>
    rcases ParStep.diamond h₁ h₂ with ⟨t', h₃, h₄⟩
    rcases ih h₄ with ⟨t'', h₅, h₆⟩
    exists t''
    constructor
    · constructor <;> assumption
    · assumption

lemma MultiParStep.diamond :
  t ⟹* t₁ → t ⟹* t₂ → ∃ t', t₁ ⟹* t' ∧ t₂ ⟹* t' := by
  intros h₁ h₂
  induction h₁ generalizing t₂ with
  | refl =>
    exists t₂
    constructor
    · exact h₂
    · constructor
  | step h₁ _ ih =>
    rcases MultiParStep.stripe h₁ h₂ with ⟨t', h₃, h₄⟩
    rcases ih h₃ with ⟨t'', h₅, h₆⟩
    exists t''
    constructor
    · assumption
    · constructor <;> assumption

theorem church_rosser :
  t ⟶* t₁ → t ⟶* t₂ → ∃ t', t₁ ⟶* t' ∧ t₂ ⟶* t' := by
  simp [←MultiParStep.iff_multi_step]
  apply MultiParStep.diamond



def Normal (t : Term n) := ∀ t', ¬ t ⟶ t'

theorem progress (t : Term n) : Normal t ∨ ∃ t', t ⟶ t' := by
  induction t with
  | var x | bool b => left; intros t h; cases h
  | lam T t ih =>
    rcases ih with h | ⟨t', h⟩
    · left; intros t' h; cases h; apply h; assumption
    · right; exists λ' T t'; constructor; assumption
  | app t₁ t₂ ih₁ ih₂ =>
    rcases ih₁ with h₁ | ⟨t', h₁⟩
    · rcases ih₂ with h₂ | ⟨t', h₂⟩
      · cases t₁
        case lam =>
          right; refine ⟨_, Step.beta⟩
        all_goals
          left
          intros t' h
          cases h <;> aesop
      · right; exists t₁ ⬝ t'; constructor; assumption
    · right; exists t' ⬝ t₂; constructor; assumption
  | pair t₁ t₂ ih₁ ih₂ =>
    rcases ih₁ with h₁ | ⟨t', h₁⟩
    · rcases ih₂ with h₂ | ⟨t', h₂⟩
      · left; intros t' h; cases h <;> aesop
      · right; exists ⟪t₁, t'⟫; constructor; assumption
    · right; exists ⟪t', t₂⟫; constructor; assumption
  | fst t ih =>
    rcases ih with h | ⟨t', h⟩
    · cases t
      case pair =>
        right; refine ⟨_, Step.sigma₁⟩
      all_goals
        left
        intros t' h
        cases h; aesop
    · right; exists t'.fst; constructor; assumption
  | snd t ih =>
    rcases ih with h | ⟨t', h⟩
    · cases t
      case pair =>
        right; refine ⟨_, Step.sigma₂⟩
      all_goals
        left
        intros t' h
        cases h; aesop
    · right; exists t'.snd; constructor; assumption
