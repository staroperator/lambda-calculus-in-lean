import Lambda.Prelude
import Lambda.Fin

namespace SystemT

inductive Ty where
| bool : Ty
| nat : Ty
| fn : Ty → Ty → Ty
| prod : Ty → Ty → Ty
infixr:70 " ⇒ " => Ty.fn
instance : Mul Ty := ⟨Ty.prod⟩
@[match_pattern] abbrev TBool := Ty.bool
@[match_pattern] abbrev TNat := Ty.nat

def Con := List Ty
@[match_pattern] def Con.add (Γ : Con) (T : Ty) := T :: Γ
instance : EmptyCollection Con := ⟨[]⟩
infixl:60 ",' " => Con.add



inductive Term : Con → Ty → Type where
| var : T ∈' Γ → Term Γ T
| lam : Term (Γ,' T₁) T₂ → Term Γ (T₁ ⇒ T₂)
| app : Term Γ (T₁ ⇒ T₂) → Term Γ T₁ → Term Γ T₂
| true : Term Γ TBool
| false : Term Γ TBool
| ite : Term Γ TBool → Term Γ T → Term Γ T → Term Γ T
| zero : Term Γ TNat
| succ : Term Γ TNat → Term Γ TNat
| recn : Term Γ TNat → Term Γ T → Term Γ (TNat ⇒ T ⇒ T) → Term Γ T
| pair : Term Γ T₁ → Term Γ T₂ → Term Γ (T₁ * T₂)
| fst : Term Γ (T₁ * T₂) → Term Γ T₁
| snd : Term Γ (T₁ * T₂) → Term Γ T₂
prefix:max "#" => Term.var
notation:max "#'" n:max => Term.var (List.Fin.ofNat n)
notation "λ'" => Term.lam
infixl:80 " ⬝ " => Term.app
notation "⟪" t₁ ", " t₂ "⟫" => Term.pair t₁ t₂

@[simp] def Term.ofNat : Nat → Term Γ TNat
| 0 => zero
| n + 1 => succ (ofNat n)
instance : OfNat (Term Γ TNat) n := ⟨Term.ofNat n⟩

def Term.rank : Term Γ T → Nat
| #x | true | false | zero => 0
| λ' t | succ t | fst t | snd t => t.rank + 1
| t₁ ⬝ t₂ | ⟪t₁, t₂⟫ => t₁.rank + t₂.rank + 1
| ite t₁ t₂ t₃ | recn t₁ t₂ t₃ => t₁.rank + t₂.rank + t₃.rank + 1

theorem Term.strong_induction {P : Term Γ T → Prop} :
  (∀ t, (∀ t', t'.rank < t.rank → P t') → P t) → ∀ t, P t := by
  intro ih
  suffices h : ∀ n t, t.rank ≤ n → P t by
    intro t; apply h (rank t); apply Nat.le_refl
  intro n
  induction' n with n ih'
  · intros t h; apply ih; intros t' h'
    exfalso; apply Nat.not_lt_zero ; exact Nat.lt_of_lt_of_le h' h
  · intros t h; apply ih; intros t' h'
    apply ih'; apply Nat.le_of_lt_succ; exact Nat.lt_of_lt_of_le h' h



inductive Weaken : Con → Con → Type where
| nil : Weaken ∅ ∅
| step : Weaken Γ Δ → Weaken Γ (Δ,' T)
| lift : Weaken Γ Δ → Weaken (Γ,' T) (Δ,' T)
infix:50 " ⊆ʷ " => Weaken
notation "εʷ" => Weaken.nil
prefix:max "↑ʷ" => Weaken.step
prefix:max "⇑ʷ" => Weaken.lift

def Weaken.id : Γ ⊆ʷ Γ :=
  match Γ with
  | [] => εʷ
  | _,' _ => ⇑ʷid
notation "idʷ" => Weaken.id

@[simp] def Weaken.apply : Γ ⊆ʷ Δ → T ∈' Γ → T ∈' Δ
| ↑ʷρ, x => fs (ρ.apply x)
| ⇑ʷρ, fz => fz
| ⇑ʷρ, fs x => fs (ρ.apply x)

@[simp] lemma Weaken.id_apply : idʷ.apply x = x := by
  rename Con => Γ
  induction' Γ with Γ T ih <;> simp [Weaken.id]
  · cases x
  · cases' x with _ _ _ x
    · rfl
    · simp [Weaken.id, ih]

@[simp] def Term.weaken : Term Γ T → Γ ⊆ʷ Δ → Term Δ T
| #x, ρ => #(ρ.apply x)
| λ' t, ρ => λ' (t.weaken ⇑ʷρ)
| t₁ ⬝ t₂, ρ => t₁.weaken ρ ⬝ t₂.weaken ρ
| true, _ => true
| false, _ => false
| ite t₁ t₂ t₃, ρ => ite (t₁.weaken ρ) (t₂.weaken ρ) (t₃.weaken ρ)
| zero, _ => zero
| succ t, ρ => succ (t.weaken ρ)
| recn t₁ t₂ t₃, ρ => recn (t₁.weaken ρ) (t₂.weaken ρ) (t₃.weaken ρ)
| ⟪t₁, t₂⟫, ρ => ⟪t₁.weaken ρ, t₂.weaken ρ⟫
| fst t, ρ => fst (t.weaken ρ)
| snd t, ρ => snd (t.weaken ρ)
notation t "[" ρ "]ʷ" => Term.weaken t ρ

theorem Term.weaken_id : t[idʷ]ʷ = t := by
  induction t <;> simp <;> aesop

def Term.shift (t : Term Γ T) : Term (Γ,' T') T := t[↑ʷidʷ]ʷ
prefix:max "↑ₜ" => Term.shift

def Weaken.comp : Γ ⊆ʷ Δ → Δ ⊆ʷ Θ → Γ ⊆ʷ Θ
| ρ, εʷ => ρ
| ρ₁, ↑ʷρ₂ => ↑ʷ(ρ₁.comp ρ₂)
| ↑ʷρ₁, ⇑ʷρ₂ => ↑ʷ(ρ₁.comp ρ₂)
| ⇑ʷρ₁, ⇑ʷρ₂ => ⇑ʷ(ρ₁.comp ρ₂)
infix:70 " ∘ʷ " => Weaken.comp

lemma Weaken.comp_apply {ρ₁ : Γ ⊆ʷ Δ} :
  (ρ₁ ∘ʷ ρ₂).apply x = ρ₂.apply (ρ₁.apply x) := by
  induction ρ₂ generalizing Γ <;>
    cases ρ₁ <;> (try cases x) <;> simp [Weaken.comp] <;> aesop

theorem Term.weaken_comp {ρ₂ : Δ ⊆ʷ Θ} :
  t[ρ₁]ʷ[ρ₂]ʷ = t[ρ₁ ∘ʷ ρ₂]ʷ := by
  induction t generalizing Δ Θ ρ₂ <;> simp
  case var => simp [Weaken.comp_apply]
  all_goals aesop



def Subst (Γ Δ : Con) := ∀ ⦃T⦄, T ∈' Γ → Term Δ T

def Subst.head (σ : Subst (Γ,' T) Δ) : Term Δ T := σ fz
def Subst.tail (σ : Subst (Γ,' T) Δ) : Subst Γ Δ := λ _ x => σ (fs x)

def Subst.id : Subst Γ Γ := λ _ => Term.var
notation "idₛ" => Subst.id

def Subst.lift (σ : Subst Γ Δ) : Subst (Γ,' T) (Δ,' T)
| _, fz => #fz
| _, fs x => ↑ₜ(σ x)
prefix:max "⇑" => Subst.lift

def Subst.single (t : Term Γ T) : Subst (Γ,' T) Γ
| _, fz => t
| _, fs x => #x
prefix:max "↦ " => Subst.single

@[simp] def Term.subst : Term Γ T → Subst Γ Δ → Term Δ T
| #x, σ => σ x
| λ' t, σ => λ' (t.subst ⇑σ)
| t₁ ⬝ t₂, σ => t₁.subst σ ⬝ t₂.subst σ
| true, _ => true
| false, _ => false
| ite t₁ t₂ t₃, σ => ite (t₁.subst σ) (t₂.subst σ) (t₃.subst σ)
| zero, _ => zero
| succ t, σ => succ (t.subst σ)
| recn t₁ t₂ t₃, σ => recn (t₁.subst σ) (t₂.subst σ) (t₃.subst σ)
| ⟪t₁, t₂⟫, σ => ⟪t₁.subst σ, t₂.subst σ⟫
| fst t, σ => fst (t.subst σ)
| snd t, σ => snd (t.subst σ)
notation t "[" σ "]ˢ" => Term.subst t σ

lemma Term.subst_id : t[idₛ]ˢ = t := by
  induction t
  case lam _ ih =>
    simp
    conv => rhs; rw [←ih]
    congr
    funext _ x
    cases x <;> simp [Subst.lift, Subst.id, Term.shift]
  all_goals aesop

def Weaken.ofSubst (ρ : Γ ⊆ʷ Δ) : Subst Γ Δ :=
  λ _ => Term.var ∘ ρ.apply
instance : Coe (Γ ⊆ʷ Δ) (Subst Γ Δ) := ⟨Weaken.ofSubst⟩

theorem Weaken.lift_of_subst :
  (⇑ʷρ : Γ,' T ⊆ʷ Δ,' T).ofSubst = ⇑ρ.ofSubst := by
  funext _ x
  cases x <;> simp [Weaken.ofSubst, Subst.lift, Term.shift]

theorem Term.weaken_eq_subst {ρ : Γ ⊆ʷ Δ} : t[ρ]ʷ = t[ρ]ˢ := by
  induction t generalizing Δ
  case lam t ih =>
    simp [ih]
    congr
    funext _ x
    cases x
    · rfl
    · simp [Weaken.ofSubst, Subst.lift, Term.shift]
  all_goals aesop

def Subst.comp (σ₁ : Subst Γ Δ) (σ₂ : Subst Δ Θ) : Subst Γ Θ :=
  λ _ x => (σ₁ x)[σ₂]ˢ
infix:70 " ∘ₛ " => Subst.comp

lemma Term.weaken_comp_subst {σ : Subst Δ Θ} :
  t[ρ]ʷ[σ]ˢ = t[ρ ∘ₛ σ]ˢ := by
  induction t generalizing Δ Θ
  case lam _ ih =>
    simp [ih]
    congr
    funext _ x
    cases x
    · rfl
    · simp [Subst.comp, Subst.lift]
  all_goals aesop

lemma Term.subst_comp_weaken {ρ : Δ ⊆ʷ Θ} :
  t[σ]ˢ[ρ]ʷ = t[σ ∘ₛ ρ]ˢ := by
  induction t generalizing Δ Θ
  case var x => simp [Term.weaken, Subst.comp, weaken_eq_subst]
  case lam _ ih =>
    simp [ih]
    congr
    funext _ x
    cases' x with _ _ x
    · rfl
    · simp [Subst.comp, Subst.lift, Term.shift]
      conv =>
        rhs
        rw [weaken_eq_subst]
        arg 1
        rw [←weaken_eq_subst]
      simp [weaken_comp_subst]
      congr
      funext x
      cases x <;> simp [Subst.comp, Weaken.ofSubst]
  all_goals aesop

theorem Term.shift_subst_lift :
  (↑ₜt : Term (Γ,' T') T)[⇑σ]ˢ = ↑ₜ(t[σ]ˢ) := by
  simp [Term.shift, weaken_comp_subst, subst_comp_weaken]
  congr
  funext x
  simp [Subst.comp, Subst.lift, Term.shift, weaken_eq_subst]

theorem Term.subst_comp {σ₂ : Subst Δ Θ} :
  t[σ₁]ˢ[σ₂]ˢ = t[σ₁ ∘ₛ σ₂]ˢ := by
  induction t generalizing Δ Θ
  case lam _ ih =>
    simp [ih]
    congr
    funext _ x
    cases x
    · rfl
    · simp [Subst.comp, Term.shift]
      apply shift_subst_lift
  all_goals aesop

theorem Term.shift_subst_single : (↑ₜt)[↦ t']ˢ = t := by
  simp [Term.shift, weaken_comp_subst]
  conv => rhs; rw [←subst_id (t := t)]
  congr
  funext x
  cases x <;> simp [Subst.comp, Subst.single, Subst.id]

lemma substitution :
  t[↦ t']ˢ[σ]ˢ = t[⇑σ]ˢ[↦ (t'[σ]ˢ)]ˢ := by
  simp [Term.subst_comp]
  congr
  funext _ x
  cases x
  · rfl
  · simp [Subst.comp, Subst.lift, Term.shift_subst_single]

lemma substitution_weaken :
  t[↦ t']ˢ[ρ]ʷ = t[⇑ʷρ]ʷ[↦ (t'[ρ]ʷ)]ˢ := by
  simp [Term.weaken_eq_subst, Weaken.lift_of_subst]
  apply substitution

end SystemT
