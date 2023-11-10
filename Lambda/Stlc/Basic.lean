import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.SolveByElim
import Aesop
import Lambda.Fin

open Fin'

inductive Ty where
| bool : Ty
| fn : Ty → Ty → Ty
| prod : Ty → Ty → Ty

infix:70 " ⇒ " => Ty.fn
instance : Mul Ty := ⟨Ty.prod⟩

inductive Context : Nat → Type where
| nil : Context 0
| cons : Context n → Ty → Context (n + 1)
instance : EmptyCollection (Context 0) := ⟨Context.nil⟩
infix:60 " ,' " => Context.cons

def Context.get : Context n → Fin' n → Ty
| _,' T, fz => T
| Γ,' _, fs x => Γ.get x



inductive Term : Nat → Type where
| var : Fin' n → Term n
| lam : Ty → Term (n + 1) → Term n
| app : Term n → Term n → Term n
| pair : Term n → Term n → Term n
| fst : Term n → Term n
| snd : Term n → Term n
| bool : Bool → Term n
prefix:max "#" => Term.var
notation "λ'" => Term.lam
infix:80 " ⬝ " => Term.app
notation "⟪" t₁ ", " t₂ "⟫" => Term.pair t₁ t₂



inductive Weaken : Nat → Nat → Type where
| nil : Weaken 0 0
| step : Weaken n m → Weaken n (m + 1)
| lift : Weaken n m → Weaken (n + 1) (m + 1)
notation "εʷ" => Weaken.nil
prefix:max "↑ʷ" => Weaken.step
prefix:max "⇑ʷ" => Weaken.lift

def Weaken.id : Weaken n n :=
  match n with
  | 0 => Weaken.nil
  | _ + 1 => Weaken.lift Weaken.id
notation "idʷ" => Weaken.id

@[simp] def Weaken.apply : Weaken n m → Fin' n → Fin' m
| ↑ʷρ, x => fs (ρ.apply x)
| ⇑ʷρ, fz => fz
| ⇑ʷρ, fs x => fs (ρ.apply x)

instance : CoeFun (Weaken n m) (λ _ => Fin' n → Fin' m) := ⟨Weaken.apply⟩

@[simp] lemma Weaken.id_apply {x : Fin' n} : idʷ x = x := by
  induction' n with n ih
  · cases x
  · cases' x with _ _ x
    · rfl
    · simp [Weaken.id, ih]

inductive Context.Weaken : Context n → Weaken n m → Context m → Prop where
| nil : Context.Weaken ∅ εʷ ∅
| step : Context.Weaken Γ ρ Δ → Context.Weaken Γ ↑ʷρ (Δ,' p)
| lift : Context.Weaken Γ ρ Δ → Context.Weaken (Γ,' p) ⇑ʷρ (Δ,' p)
notation Γ " ⊆[" ρ "] " Δ:50 => Context.Weaken Γ ρ Δ

theorem Context.weaken_id : Γ ⊆[idʷ] Γ := by
  induction Γ <;> constructor; assumption

@[simp] def Term.weaken : Term n → Weaken n m → Term m
| #x, ρ => #(ρ x)
| λ' T t, ρ => λ' T (t.weaken ⇑ʷρ)
| t₁ ⬝ t₂, ρ => t₁.weaken ρ ⬝ t₂.weaken ρ
| ⟪t₁, t₂⟫, ρ => ⟪t₁.weaken ρ, t₂.weaken ρ⟫
| fst t, ρ => fst (t.weaken ρ)
| snd t, ρ => snd (t.weaken ρ)
| bool b, _ => bool b
notation t "[" ρ "]ʷ" => Term.weaken t ρ

theorem Term.weaken_id : t[idʷ]ʷ = t := by
  induction t <;> simp <;> aesop

def Term.shift (t : Term n) : Term (n + 1) := t[↑ʷidʷ]ʷ
prefix:max "↑ₜ" => Term.shift

@[simp] lemma Theorem.shift_var : ↑ₜ#x = #(fs x) := by
  simp [Term.shift]

def Weaken.comp : Weaken n m → Weaken m k → Weaken n k
| ρ, εʷ => ρ
| ρ₁, ↑ʷρ₂ => ↑ʷ(ρ₁.comp ρ₂)
| ↑ʷρ₁, ⇑ʷρ₂ => ↑ʷ(ρ₁.comp ρ₂)
| ⇑ʷρ₁, ⇑ʷρ₂ => ⇑ʷ(ρ₁.comp ρ₂)

infix:70 " ∘ʷ " => Weaken.comp

lemma Weaken.comp_apply {ρ₁ : Weaken n m} : (ρ₁ ∘ʷ ρ₂) x = ρ₂ (ρ₁ x) := by
  induction ρ₂ generalizing n <;>
    cases ρ₁ <;> (try cases x) <;> simp [Weaken.comp] <;> aesop

theorem Term.weaken_comp {ρ₂ : Weaken m k} :
  t[ρ₁]ʷ[ρ₂]ʷ = t[ρ₁ ∘ʷ ρ₂]ʷ := by
  induction t generalizing m k ρ₂ <;> simp
  case var => simp [Weaken.comp_apply]
  all_goals aesop

theorem Context.weaken_comp {ρ₁ : _root_.Weaken n m} :
  Γ ⊆[ρ₁] Δ → Δ ⊆[ρ₂] Θ → Γ ⊆[ρ₁ ∘ʷ ρ₂] Θ := by
  intros h₁ h₂
  induction h₂ generalizing n <;> cases h₁ <;>
    repeat (first | constructor | apply_assumption)



def Subst (n m) := Fin' n → Term m

def Subst.id : Subst n n := Term.var
notation "idₛ" => Subst.id

def Subst.lift (σ : Subst n m) : Subst (n + 1) (m + 1)
| fz => #fz
| fs x => ↑ₜ(σ x)
prefix:max "⇑" => Subst.lift

def Subst.single (t : Term n) : Subst (n + 1) n
| fz => t
| fs x => #x
prefix:max "↦ " => Subst.single

@[simp] def Term.subst : Term n → Subst n m → Term m
| #x, σ => σ x
| λ' T t, σ => λ' T (t.subst ⇑σ)
| t₁ ⬝ t₂, σ => t₁.subst σ ⬝ t₂.subst σ
| ⟪t₁, t₂⟫, σ => ⟪t₁.subst σ, t₂.subst σ⟫
| fst t, σ => fst (t.subst σ)
| snd t, σ => snd (t.subst σ)
| bool b, _ => bool b
notation t "[" σ "]" => Term.subst t σ

lemma Term.subst_id {t : Term n} : t[idₛ] = t := by
  induction t
  case lam _ ih =>
    simp
    conv => rhs; rw [←ih]
    congr
    funext x
    cases x <;> simp [Subst.lift, Subst.id]
  all_goals aesop

def Weaken.ofSubst (ρ : Weaken n m) : Subst n m := Term.var ∘ ρ.apply

instance : Coe (Weaken n m) (Subst n m) := ⟨Weaken.ofSubst⟩

theorem Weaken.lift_of_subst : ⇑ʷρ = ⇑ρ.ofSubst := by
  funext x
  cases x <;> simp [Weaken.ofSubst, Subst.lift]

theorem Term.weaken_eq_subst {ρ : Weaken n m} : t[ρ]ʷ = t[ρ] := by
  induction t generalizing m
  case lam _ ih =>
    simp [ih]
    congr
    funext x
    cases x
    · rfl
    · simp [Weaken.ofSubst, Subst.lift]
  all_goals aesop

def Subst.comp (σ₁ : Subst n m) (σ₂ : Subst m k) : Subst n k :=
  λ x => (σ₁ x)[σ₂]
infix:70 " ∘ₛ " => Subst.comp

lemma Term.weaken_comp_subst {ρ : Weaken n m} {σ : Subst m k} :
  t[ρ]ʷ[σ] = t[ρ ∘ₛ σ] := by
  induction t generalizing m k
  case lam _ ih =>
    simp [ih]
    congr
    funext x
    cases x
    · rfl
    · simp [Subst.comp, Subst.lift]
  all_goals aesop

lemma Term.subst_comp_weaken {t : Term n} {σ : Subst n m} {ρ : Weaken m k} :
  t[σ][ρ]ʷ = t[σ ∘ₛ ρ] := by
  induction t generalizing m k
  case var x => simp [Term.weaken, Subst.comp, weaken_eq_subst]
  case lam _ ih =>
    simp [ih]
    congr
    funext x
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

theorem Term.shift_subst_lift : (↑ₜt)[⇑σ] = ↑ₜ(t[σ]) := by
  simp [Term.shift, weaken_comp_subst, subst_comp_weaken]
  congr
  funext x
  simp [Subst.comp, Subst.lift, Term.shift, weaken_eq_subst]

theorem Term.subst_comp {t : Term n} {σ₁ : Subst n m} {σ₂ : Subst m k} :
  t[σ₁][σ₂] = t[σ₁ ∘ₛ σ₂] := by
  induction t generalizing m k
  case lam _ ih =>
    simp [ih]
    congr
    funext x
    cases x
    · rfl
    · simp [Subst.comp, Term.shift]
      repeat conv in (⇑_ _) => simp [Subst.lift]
      apply shift_subst_lift
  all_goals aesop

theorem Term.shift_subst_single : (↑ₜt)[↦ t'] = t := by
  simp [Term.shift, weaken_comp_subst]
  conv => rhs; rw [←subst_id (t := t)]
  congr
  funext x
  cases x <;> simp [Subst.comp, Subst.single, Subst.id]

lemma substitution {t : Term (n + 1)} {σ : Subst n m} :
  t[↦ t'][σ] = t[⇑σ][↦ (t'[σ])] := by
  simp [Term.subst_comp]
  congr
  funext x
  cases x
  · rfl
  · simp [Subst.comp, Subst.lift, Term.shift_subst_single]

lemma substitution_weaken {t : Term (n + 1)} :
  t[↦ t'][ρ]ʷ = t[⇑ʷρ]ʷ[↦ (t'[ρ]ʷ)] := by
  simp [Term.weaken_eq_subst, Weaken.lift_of_subst]
  apply substitution
