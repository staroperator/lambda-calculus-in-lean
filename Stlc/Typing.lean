import Stlc.Basic

inductive Typing : Context n → Term n → Ty → Prop where
| var : Typing Γ #x (Γ.get x)
| lam : Typing (Γ,' T₁) t T₂ → Typing Γ (λ' T₁ t) (T₁ ⇒ T₂)
| app : Typing Γ t₁ (T₁ ⇒ T₂) → Typing Γ t₂ T₁ → Typing Γ (t₁ ⬝ t₂) T₂
| pair : Typing Γ t₁ T₁ → Typing Γ t₂ T₂ → Typing Γ ⟪t₁, t₂⟫ (T₁ * T₂)
| fst : Typing Γ t (T₁ * T₂) → Typing Γ t.fst T₁
| snd : Typing Γ t (T₁ * T₂) → Typing Γ t.snd T₂
| bool : Typing Γ (Term.bool b) Ty.bool
notation:50 Γ " ⊢ " t " : " T:50 => Typing Γ t T

theorem Typing.uniqueness : Γ ⊢ t : T₁ → Γ ⊢ t : T₂ → T₁ = T₂ := by
  intros h₁ h₂
  induction h₁ generalizing T₂
  case lam _ ih =>
    cases h₂; case lam h₂ =>
    apply ih at h₂
    simp [h₂]
  case app h₁ ih =>
    cases h₂; case app h₂ h₃ =>
    apply ih at h₂
    apply h₁ at h₃
    injection h₃
  case fst _ ih =>
    cases h₂; case fst h₂ =>
    apply ih at h₂
    injection h₂
  case snd _ ih =>
    cases h₂; case snd h₂ =>
    apply ih at h₂
    injection h₂
  all_goals (cases h₂; congr <;> aesop)

lemma Typing.inversion_var : Γ ⊢ #x : T → T = Γ.get x := by
  intro h; cases h; rfl

theorem Typing.weaken {ρ : Weaken n m} :
  Γ ⊆[ρ] Δ → Γ ⊢ t : T → Δ ⊢ t[ρ]ʷ : T := by
  intros h₁ h₂
  induction h₂ generalizing m Δ
  case var x =>
    induction h₁
    case nil => cases x
    case step _ ih =>
      rw [Typing.inversion_var (@ih x)]
      constructor
    case lift _ ih =>
      cases' x with _ _ x
      · constructor
      · simp [Context.get, Typing.inversion_var (@ih x)]
        constructor
  case lam _ ih =>
    constructor
    apply ih
    constructor
    assumption
  all_goals (constructor <;> aesop)

theorem Typing.weaken_single : Γ ⊢ t : T → Γ,' T' ⊢ ↑ₜt : T := by
  apply Typing.weaken
  constructor
  exact Context.weaken_id

theorem Typing.strengthen {ρ : Weaken n m} :
  Γ ⊆[ρ] Δ → Δ ⊢ t[ρ]ʷ : T → Γ ⊢ t : T := by
  intros h₁ h₂
  generalize h : t[ρ]ʷ = t' at h₂
  induction h₂ generalizing n Γ t
  case var x =>
    induction h₁
    case nil => cases x
    case step _ ih =>
      cases t <;> simp at h
      cases x <;> simp at h
      apply ih
      simp [h]
    case lift _ ih =>
      cases' t with _ y <;> simp at h
      cases' x with _ _ x
      · cases y <;> simp at h
        constructor
      · cases' y with _ _ y <;> simp at h
        simp [Context.get, Typing.inversion_var (ih (by simp; exact h))]
        constructor
  case lam _ ih =>
    cases t <;> simp at h
    rcases h with ⟨h, h'⟩
    subst h h'
    constructor
    apply ih
    · apply Context.Weaken.lift
      assumption
    · simp
  all_goals
    cases t <;> simp at h
    (try cases h)
    constructor <;> apply_assumption <;> first | rfl | assumption
    
theorem Typing.strengthen_single : Γ,' T' ⊢ ↑ₜt : T → Γ ⊢ t : T := by
  apply Typing.strengthen
  constructor
  exact Context.weaken_id



def Context.Typing (Γ : Context m) (σ : Subst n m) (Δ : Context n) :=
  ∀ x, Γ ⊢ σ x : Δ.get x
notation:50 Γ " ⊢ " σ " :ₛ " Δ:50 => Context.Typing Γ σ Δ

theorem Typing.cut {σ : Subst n m} :
  Γ ⊢ σ :ₛ Δ → Δ ⊢ t : T → Γ ⊢ t[σ] : T := by
  intros h₁ h₂
  induction h₂ generalizing m <;> simp
  case var =>
    apply h₁
  case lam _ ih =>
    constructor
    apply ih
    intro x
    cases' x with _ _ x
    · constructor
    · simp [Context.get, Subst.lift]
      apply Typing.weaken_single
      apply h₁
  all_goals
    constructor <;> aesop

theorem Typing.cut_single : Γ ⊢ t' : T' → Γ,' T' ⊢ t : T → Γ ⊢ t[↦ t'] : T := by
  intro h
  apply Typing.cut
  intro x
  cases' x with _ _ x
  · exact h
  · constructor
