import Lambda.PCF.Syntax
import Lambda.Rel

namespace PCF

open Term in
@[aesop unsafe constructors]
inductive Step : Rel (Term Γ T) where
| lam : Step t t' → Step (λ' t) (λ' t')
| app₁ : Step t₁ t₁' → Step (t₁ ⬝ t₂) (t₁' ⬝ t₂)
| app₂ : Step t₂ t₂' → Step (t₁ ⬝ t₂) (t₁ ⬝ t₂')
| beta : Step (λ' t₁ ⬝ t₂) (t₁[↦ t₂]ˢ)
| fix₁ : Step t t' → Step (fix t) (fix t')
| fix₂ : Step (fix t) (t ⬝ fix t)
| ite₁ : Step t₁ t₁' → Step (ite t₁ t₂ t₃) (ite t₁' t₂ t₃)
| ite₂ : Step t₂ t₂' → Step (ite t₁ t₂ t₃) (ite t₁ t₂' t₃)
| ite₃ : Step t₃ t₃' → Step (ite t₁ t₂ t₃) (ite t₁ t₂ t₃')
| ite_true : Step (Term.ite true t₁ t₂) t₁
| ite_false : Step (Term.ite false t₁ t₂) t₂
| succ : Step t t' → Step (succ t) (succ t')
| succ_nat : Step (succ (nat n)) (nat (n + 1))
| pred : Step t t' → Step (pred t) (pred t')
| pred_zero : Step (pred (nat 0)) (nat 0)
| pred_succ : Step (pred (nat (n + 1))) (nat n)
| isz : Step t t' → Step (isz t) (isz t')
| isz_zero : Step (isz (nat 0)) true
| isz_succ : Step (isz (nat (n + 1))) false
| pair₁ : Step t₁ t₁' → Step ⟪t₁, t₂⟫ ⟪t₁', t₂⟫
| pair₂ : Step t₂ t₂' → Step ⟪t₁, t₂⟫ ⟪t₁, t₂'⟫
| fst : Step t t' → Step (fst t) (fst t')
| sigma₁ : Step (fst ⟪t₁, t₂⟫) t₁
| snd : Step t t' → Step (snd t) (snd t')
| sigma₂ : Step (snd ⟪t₁, t₂⟫) t₂
infix:55 " ⟶ " => Step

lemma Step.weaken {ρ : Weaken n m} :
  t ⟶ t' → t[ρ]ʷ ⟶ t'[ρ]ʷ := by
  intro h
  induction h generalizing m <;> simp
  case beta =>
    rw [substitution_weaken]
    constructor
  all_goals constructor <;> aesop

lemma Step.subst {σ : Subst Γ Δ} : t ⟶ t' → t[σ]ˢ ⟶ t'[σ]ˢ := by
  intro h
  induction h generalizing Δ <;> simp
  case beta =>
    rw [substitution]
    constructor
  all_goals constructor <;> aesop



def Reduce : Rel (Term Γ T) := Step.Multi
infix:55 " ⟶* " => Reduce

def DefEquiv : Rel (Term Γ T) := Step.Equiv
infix:55 " ≡ " => DefEquiv



theorem Step.plug {C : Context Γ T Δ T'} :
  t ⟶ t' → C.plug t ⟶ C.plug t' := by
  intro h
  induction C <;> simp [Context.plug] <;> aesop

theorem Reduce.plug {C : Context Γ T Δ T'} :
  t ⟶* t' → C.plug t ⟶* C.plug t' := by
  intro h
  induction h with
  | refl => exact Rel.Multi.refl
  | step h _ ih => exact Rel.Multi.step (Step.plug h) ih

theorem DefEquiv.plug {C : Context Γ T Δ T'} :
  t ≡ t' → C.plug t ≡ C.plug t' := by
  intro h
  induction h with
  | refl => exact Rel.Equiv.refl
  | symm _ ih => exact Rel.Equiv.symm ih
  | trans _ _ ih₁ ih₂ => exact Rel.Equiv.trans ih₁ ih₂
  | step h => exact Rel.Equiv.step (Step.plug h)

def Value : Term ∅ T → Prop
| Term.true | Term.false | Term.nat _ => True
| _ => False

def ContextApprox (t₁ t₂ : Term Γ T) :=
  ∀ T' (C : Context Γ T ∅ T') (v : Term ∅ T'),
  Value v → C.plug t₁ ⟶* v → C.plug t₂ ⟶* v
infix:55 " ≲ᶜ " => ContextApprox

def ContextEquiv (t₁ t₂ : Term Γ T) :=
  ∀ T' (C : Context Γ T ∅ T') (v : Term ∅ T'),
  Value v → (C.plug t₁ ⟶* v ↔ C.plug t₂ ⟶* v)
infix:55 " ≈ᶜ " => ContextEquiv

theorem ContextEquiv.approx : t₁ ≈ᶜ t₂ → t₁ ≲ᶜ t₂ := by
  intro h T' C v h₁ h₂
  rw [←h T' C v h₁]
  exact h₂

end PCF
