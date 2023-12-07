import Lambda.STLC.Operational

open List.Fin (fz fs)

namespace STLC

def Ty.denot : Ty → Type
| TBool => Bool
| T₁ ⇒ T₂ => T₁.denot → T₂.denot
| T₁ * T₂ => T₁.denot × T₂.denot
notation "⟦" T "⟧ᵀ" => Ty.denot T

def Con.denot : Con → Type
| [] => Unit
| Γ,' T => Γ.denot × ⟦T⟧ᵀ
notation "⟦" Γ "⟧ᴳ" => Con.denot Γ

def Con.denot_get : T ∈' Γ → ⟦Γ⟧ᴳ → ⟦T⟧ᵀ
| fz, ⟨_, d⟩ => d
| fs x, ⟨d, _⟩ => denot_get x d

lemma Con.denot_ext :
  (∀ {T} (x : T ∈' Γ), Con.denot_get x d₁ = Con.denot_get x d₂) →
  d₁ = d₂ := by
  intro h
  induction Γ with
  | nil => rfl
  | cons Γ T ih =>
    cases d₁; cases d₂
    congr
    · apply ih; intros _ x; apply h (fs x)
    · apply h fz

def Term.denot : Term Γ T → ⟦Γ⟧ᴳ → ⟦T⟧ᵀ
| #x, d => Con.denot_get x d
| λ' t, d₁ => λ d₂ => t.denot ⟨d₁, d₂⟩
| t₁ ⬝ t₂, d => t₁.denot d (t₂.denot d)
| true, _ => Bool.true
| false, _ => Bool.false
| ite t₁ t₂ t₃, d =>
  match t₁.denot d with
  | Bool.true => t₂.denot d
  | Bool.false => t₃.denot d
| ⟪t₁, t₂⟫, d => ⟨t₁.denot d, t₂.denot d⟩
| fst t, d => (t.denot d).fst
| snd t, d => (t.denot d).snd
notation "⟦" t "⟧ᵗ" => Term.denot t

def Weaken.denot : Γ ⊆ʷ Δ → ⟦Δ⟧ᴳ → ⟦Γ⟧ᴳ
| εʷ, () => ()
| ↑ʷρ, ⟨d, _⟩ => ρ.denot d
| ⇑ʷρ, ⟨d₁, d₂⟩ => ⟨ρ.denot d₁, d₂⟩
notation "⟦" ρ "⟧ʷ" => Weaken.denot ρ

lemma Weaken.denot_id {d : ⟦Γ⟧ᴳ} : ⟦idʷ⟧ʷ d = d := by
  induction Γ with
  | nil => rfl
  | cons Γ T ih => cases d; simp [Weaken.id, Weaken.denot, ih]

theorem Term.denot_weaken {ρ : Γ ⊆ʷ Δ} : ⟦t[ρ]ʷ⟧ᵗ = ⟦t⟧ᵗ ∘ ⟦ρ⟧ʷ := by
  induction t generalizing Δ <;> simp [Term.weaken, Term.denot]
  case var x =>
    funext d
    induction ρ with
    | nil => cases x
    | step ρ ih => cases d; simp [Weaken.denot, Con.denot_get, ih]
    | lift ρ ih =>
      cases d; cases x <;> simp [Weaken.denot, Con.denot_get, ih]
  all_goals aesop

lemma Term.denot_shift : ⟦↑ₜt⟧ᵗ ⟨d₁, d₂⟩ = ⟦t⟧ᵗ d₁ := by
  simp [Term.shift, Term.denot_weaken, Weaken.denot, Weaken.denot_id]

def Subst.denot : {Γ : Con} → Subst Γ Δ → ⟦Δ⟧ᴳ → ⟦Γ⟧ᴳ
| [], _, _ => ()
| _,' _, σ, d => ⟨σ.tail.denot d, ⟦σ.head⟧ᵗ d⟩
notation "⟦" σ "⟧ˢ" => Subst.denot σ

lemma Subst.denot_apply {σ : Subst Γ Δ} : ⟦σ x⟧ᵗ d = (Con.denot_get x) (⟦σ⟧ˢ d) := by
  induction x with
  | fz => rfl
  | fs x ih =>
    have h := ih (σ := σ.tail)
    simp [Con.denot_get] at h
    simp [Con.denot_get, ←h]
    rfl

theorem Term.denot_subst {t : Term Γ T} {σ : Subst Γ Δ} :
  ⟦t[σ]ˢ⟧ᵗ = ⟦t⟧ᵗ ∘ ⟦σ⟧ˢ := by
  induction t generalizing Δ <;> simp [Term.subst, Term.denot]
  case var x => ext d; simp [Subst.denot_apply]
  case lam t ih =>
    ext d₁ d₂
    simp [ih, Subst.denot]
    congr 2
    apply Con.denot_ext
    intros _ x
    simp [←Subst.denot_apply, Subst.tail, Subst.lift, Term.denot_shift]
  all_goals aesop

lemma Term.denot_subst_single : ⟦t₁[↦ t₂]ˢ⟧ᵗ d = ⟦t₁⟧ᵗ ⟨d, ⟦t₂⟧ᵗ d⟩ := by
   simp [Term.denot_subst, Subst.denot]
   congr
   apply Con.denot_ext
   intro _ x
   simp [Subst.single, Subst.tail, ←Subst.denot_apply, Term.denot]

theorem Step.denot_eq : t₁ ⟶ t₂ → ⟦t₁⟧ᵗ = ⟦t₂⟧ᵗ := by
  intro h
  induction h <;> simp [Term.denot]
  case beta =>
    ext d; simp [Term.denot_subst_single]
  all_goals aesop

theorem Reduce.denot_eq : t₁ ⟶* t₂ → ⟦t₁⟧ᵗ = ⟦t₂⟧ᵗ := by
  intro h; induction h with
  | refl => rfl
  | step h _ ih => simp [ih, Step.denot_eq h]

theorem DefEquiv.denot_eq : t₁ ≡ t₂ → ⟦t₁⟧ᵗ = ⟦t₂⟧ᵗ := by
  intro h; induction h with
  | refl => rfl
  | symm _ ih => simp [ih]
  | trans _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | step h => simp [Step.denot_eq h]

theorem denot_eq_eta : ⟦t⟧ᵗ = ⟦λ' (↑ₜt ⬝ #fz)⟧ᵗ := by
  ext d; simp [Term.denot, Con.denot_get, Term.denot_shift]

end STLC
