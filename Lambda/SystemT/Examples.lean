import Lambda.SystemT.Operational
import Lambda.SystemT.Denotational
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Computability.Ackermann

namespace SystemT

open Term

@[simp] theorem Subst.lift_apply_fz : (⇑σ : Subst (_ ,' T) _) fz = #fz := rfl
@[simp] theorem Subst.lift_apply_fs : (⇑σ : Subst (_ ,' T) _) (fs x) = ↑ₜ(σ x) := rfl
@[simp] theorem Subst.single_apply_fz : (↦ t) fz = t := rfl
@[simp] theorem Subst.single_apply_fs : (↦ t) (fs x) = #x := rfl
@[simp] theorem step_eq : Step t₁ t₂ = t₁ ⟶ t₂ := rfl
@[simp] theorem reduce_eq : Rel.Multi Step t₁ t₂ = t₁ ⟶* t₂ := rfl
theorem step : t₁ ⟶ t₂ → t₂ ⟶* t₃ → t₁ ⟶* t₃ := Rel.Multi.step



def add : Term Γ (TNat ⇒ TNat ⇒ TNat) :=
  λ' (λ' (recn #'0 #'1 (λ' (λ' (succ #'0)))))

def mult : Term Γ (TNat ⇒ TNat ⇒ TNat) :=
  λ' (λ' (recn #'0 0 (λ' (λ' (add ⬝ #'0 ⬝ #'3)))))

def pred : Term Γ (TNat ⇒ TNat) :=
  λ' (recn #'0 0 (λ' (λ' #'1)))

def isz : Term Γ (TNat ⇒ TBool) :=
  λ' (recn #'0 true (λ' (λ' false)))

def fact : Term Γ (TNat ⇒ TNat) :=
  λ' (recn #'0 1 (λ' (λ' (mult ⬝ succ #'1 ⬝ #'0))))

def iter : Term Γ (TNat ⇒ (T ⇒ T) ⇒ T ⇒ T) :=
  λ' (λ' (λ' (recn #'2 #'0 (λ' (λ' #'3 ⬝ #'0)))))

def ack : Term Γ (TNat ⇒ TNat ⇒ TNat) :=
  λ' (recn #fz (λ' (succ #'0))
               (λ' (λ' (λ' (iter ⬝ #'0 ⬝ #'1 ⬝ (#'1 ⬝ 1))))))



variable {n m : Nat}

theorem add_reduce : (add : Term Γ _) ⬝ ofNat n ⬝ ofNat m ⟶* ofNat (n + m) := by
  apply step (Step.app₁ Step.beta); simp
  apply step Step.beta; simp [Term.shift_subst_single]
  induction' m with m ih
  · apply step Step.recn_zero
    exact Rel.Multi.refl
  · apply step Step.recn_succ; simp
    apply step (Step.app₁ Step.beta); simp
    apply step Step.beta; simp
    apply Rel.Multi.congr ih
    aesop

theorem mult_reduce : (mult : Term Γ _) ⬝ ofNat n ⬝ ofNat m ⟶* ofNat (n * m) := by
  apply step (Step.app₁ Step.beta); simp
  apply step Step.beta; simp [Term.shift_subst_lift, Term.shift_subst_single]
  induction' m with m ih
  · apply step Step.recn_zero
    exact Rel.Multi.refl
  · apply step Step.recn_succ
    apply step (Step.app₁ Step.beta); simp [Term.shift_subst_lift, Term.shift_subst_single]
    apply step Step.beta; simp [Term.shift_subst_single]
    apply Rel.Multi.trans
    · apply Rel.Multi.congr (f := λ t => _ ⬝ t ⬝ _) ih; aesop
    · apply add_reduce

theorem pred_reduce : (pred : Term Γ _) ⬝ ofNat n ⟶* ofNat n.pred := by
  cases' n with n
  · apply step Step.beta; simp
    apply step Step.recn_zero
    exact Rel.Multi.refl
  · apply step Step.beta; simp
    apply step Step.recn_succ
    apply step (Step.app₁ Step.beta); simp
    apply step Step.beta; simp [Term.shift_subst_single]
    exact Rel.Multi.refl

theorem isz_reduce_zero : (isz : Term Γ _) ⬝ 0 ⟶* true := by
  apply step Step.beta; simp
  apply step Step.recn_zero
  exact Rel.Multi.refl

theorem isz_reduce_succ : (isz : Term Γ _) ⬝ ofNat n.succ ⟶* false := by
  apply step Step.beta; simp
  apply step Step.recn_succ
  apply step (Step.app₁ Step.beta); simp
  apply step Step.beta; simp
  exact Rel.Multi.refl

theorem fact_reduce : (fact : Term Γ _) ⬝ ofNat n ⟶* ofNat n.factorial := by
  apply step Step.beta; simp
  induction' n with n ih
  · apply step Step.recn_zero
    exact Rel.Multi.refl
  · apply step Step.recn_succ
    apply step (Step.app₁ Step.beta); simp [Term.shift_subst_lift, Term.shift_subst_single]
    apply step Step.beta; simp [Term.shift_subst_single]
    apply Rel.Multi.trans
    · apply Rel.Multi.congr (f := λ t => _ ⬝ _ ⬝ t) ih; aesop
    · conv => arg 2; arg 1; arg 2; rw [←Term.ofNat]
      apply mult_reduce

theorem ack_reduce : (ack : Term Γ _) ⬝ ofNat n ⬝ ofNat m ⟶* ofNat (_root_.ack n m) := by
  apply step (Step.app₁ Step.beta); simp
  induction' n with n ih generalizing m
  · apply step (Step.app₁ Step.recn_zero)
    apply step Step.beta; simp
    exact Rel.Multi.refl
  · apply step (Step.app₁ Step.recn_succ)
    apply step (Step.app₁ (Step.app₁ Step.beta)); simp [Term.shift_subst_lift, Term.shift_subst_single]
    apply step (Step.app₁ Step.beta); simp [Term.shift_subst_single]
    apply step Step.beta; simp
    rw [←Term.shift, Term.shift_subst_single]
    apply step (Step.app₁ (Step.app₁ Step.beta)); simp
    apply step (Step.app₁ Step.beta); simp [Term.shift_subst_lift, Term.shift_subst_single]
    apply step Step.beta; simp [Term.shift_subst_single]
    rw [←Term.shift, Term.shift_subst_lift]
    rw [←Term.shift, Term.shift_subst_lift]
    rw [←Term.shift, Term.shift_subst_single]
    apply step (Step.recn₃ (Step.lam Step.beta)); simp [Term.shift_subst_single]
    apply Rel.Multi.trans
    · apply Rel.Multi.congr (f := λ t => recn _ t _) (ih (m := 1)); aesop
    induction' m with m ih'
    · apply step Step.recn_zero
      exact Rel.Multi.refl
    · apply step Step.recn_succ
      apply step (Step.app₁ Step.beta); simp [Term.shift_subst_single]
      apply Rel.Multi.trans
      · apply Rel.Multi.congr (f := λ t => _ ⬝ t) ih'; aesop
      apply ih



variable {d : ⟦Γ⟧ᴳ}

theorem add_denot : ⟦add⟧ᵗ d n m = n + m := by
  simp [Term.denot, Con.denot_get, Nat.recAuxOn]
  induction' m with m ih
  · rfl
  · simp [Nat.recAux, ih]; rfl

theorem mult_denot : ⟦mult⟧ᵗ d n m = n * m := by
  simp [Term.denot, Con.denot_get, Nat.recAuxOn]
  induction' m with m ih
  · rfl
  · simp [Nat.recAux, ih]
    apply add_denot (d := d)

theorem pred_denot : ⟦pred⟧ᵗ d n = n.pred := by
  cases' n with n <;> rfl

theorem isz_denot_zero : ⟦isz⟧ᵗ d Nat.zero = Bool.true := rfl
theorem isz_denot_succ : ⟦isz⟧ᵗ d (n + 1) = Bool.false := rfl

theorem fact_denot : ⟦fact⟧ᵗ d n = n.factorial := by
  simp [Term.denot, Con.denot_get, Nat.recAuxOn]
  induction' n with n ih
  · rfl
  · trans
    · apply mult_denot (d := d) (n := n + 1)
    · congr

theorem ack_denot : ⟦ack⟧ᵗ d n m = _root_.ack n m := by
  simp [Term.denot, Con.denot_get, Nat.recAuxOn]
  induction' n with n ih generalizing m
  · simp
  · induction' m with m ih'
    · simp [Nat.recAux, ih]
    · simp [Nat.recAux, ih]
      congr
      rw [←ih']
      congr
      rw [ih]

end SystemT
