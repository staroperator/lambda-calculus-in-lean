import Lambda.PCF.Operational
import Lambda.Domain

noncomputable section

namespace Domain

variable {α : Domain}

def Bool' := Flat Bool

def ite : Bool' →ᴰ α →ᴰ α →ᴰ α where
  val := λ
         | some true => K
         | some false => swap K
         | none => ⊥
  property := by
    apply Flat.mono_continuous
    intro b₁ b₂ h; simp
    split <;> split <;> cases h <;> simp

def Nat' := Flat Nat

def succ : Nat' →ᴰ Nat' where
  val := λ
         | some n => some (n + 1)
         | none => ⊥
  property := by
    apply Flat.mono_continuous
    intros x₁ x₂ h; simp
    split <;> split <;> cases h <;> simp

def pred : Nat' →ᴰ Nat' where
  val := λ
         | some 0 => some 0
         | some (n + 1) => some n
         | none => ⊥
  property := by
    apply Flat.mono_continuous
    intros x₁ x₂ h; simp
    split <;> split <;> cases h <;> constructor

def isz : Nat' →ᴰ Bool' where
  val := λ
         | some 0 => some true
         | some (_ + 1) => some false
         | none => ⊥
  property := by
    apply Flat.mono_continuous
    intros x₁ x₂ h; simp
    split <;> split <;> cases h <;> constructor

end Domain

namespace PCF

@[reducible] def Ty.Denot : Ty → Domain
| bool => Domain.Bool'
| nat => Domain.Nat'
| T₁ * T₂ => T₁.Denot ×ᴰ T₂.Denot
| fn T₁ T₂ => T₁.Denot →ᴰ T₂.Denot
notation "⟦" T "⟧ᵀ" => Ty.Denot T

instance : CoeFun (⟦T₁ ⇒ T₂⟧ᵀ) (λ _ => ⟦T₁⟧ᵀ → ⟦T₂⟧ᵀ) := ⟨Subtype.val⟩

def Con.Denot : Con → Domain
| [] => Domain.Unit
| Γ,' T => Γ.Denot ×ᴰ ⟦T⟧ᵀ
notation "⟦" Γ "⟧ᴳ" => Con.Denot Γ

def Con.denot_get : T ∈' Γ → ⟦Γ⟧ᴳ →ᴰ ⟦T⟧ᵀ
| fz => Domain.snd
| fs x => Domain.comp (denot_get x) Domain.fst

theorem Con.denot_ext {a b : ⟦Γ⟧ᴳ} :
  (∀ {T} (x : T ∈' Γ), Con.denot_get x a = Con.denot_get x b) → a = b := by
  intro h
  induction' Γ with Γ T ih
  · rfl
  · cases' a with a a'; cases' b with b b'
    congr
    · apply ih; intros T x
      replace h := h (x := fs x)
      simp [denot_get] at h
      exact h
    · replace h := h (x := fz)
      simp [denot_get] at h
      exact h

def Term.denot : Term Γ T → ⟦Γ⟧ᴳ →ᴰ ⟦T⟧ᵀ
| #x => Con.denot_get x
| λ' t => Domain.curry t.denot
| t₁ ⬝ t₂ => Domain.S t₁.denot t₂.denot
| fix t => Domain.comp Domain.fix t.denot
| true => Domain.const (some Bool.true)
| false => Domain.const (some Bool.false)
| ite t₁ t₂ t₃ => Domain.comp₃ Domain.ite t₁.denot t₂.denot t₃.denot
| nat n => Domain.const (some n)
| succ t => Domain.comp Domain.succ t.denot
| pred t => Domain.comp Domain.pred t.denot
| isz t => Domain.comp Domain.isz t.denot
| ⟪t₁, t₂⟫ => Domain.comp₂ Domain.pair t₁.denot t₂.denot
| fst t => Domain.comp Domain.fst t.denot
| snd t => Domain.comp Domain.snd t.denot
notation "⟦" t "⟧ᵗ" => Term.denot t

def Weaken.denot : Γ ⊆ʷ Δ → ⟦Δ⟧ᴳ →ᴰ ⟦Γ⟧ᴳ
| εʷ => Domain.I
| ↑ʷρ => Domain.comp ρ.denot Domain.fst
| ⇑ʷρ => Domain.uncurry (Domain.comp Domain.pair ρ.denot)
notation "⟦" ρ "⟧ʷ" => Weaken.denot ρ

lemma Weaken.denot_id : ⟦(idʷ : Γ ⊆ʷ Γ)⟧ʷ = Domain.I := by
  induction' Γ with Γ T ih
  · rfl
  · ext ⟨g, d⟩; simp [Weaken.id, Weaken.denot, ih]

theorem Term.denot_weaken {ρ : Γ ⊆ʷ Δ} :
  ⟦t[ρ]ʷ⟧ᵗ = Domain.comp ⟦t⟧ᵗ ⟦ρ⟧ʷ := by
  induction t generalizing Δ <;> simp [Term.weaken, Term.denot]
  case var x =>
    induction ρ with
    | nil => cases x
    | step ρ ih =>
      ext ⟨g, d⟩; simp [Weaken.denot, Con.denot_get, ih]
    | lift ρ ih =>
      ext ⟨g, d⟩; simp [Weaken.denot]
      cases x <;> simp [Con.denot_get, ih]
  all_goals aesop

lemma Term.denot_shift :
  ⟦(↑ₜt : Term (Γ,' T) T')⟧ᵗ = Domain.comp ⟦t⟧ᵗ Domain.fst := by
  ext ⟨g, d⟩; simp [Term.shift, Term.denot_weaken, Weaken.denot, Weaken.denot_id]

def Subst.denot (σ : Subst Γ Δ) : ⟦Δ⟧ᴳ →ᴰ ⟦Γ⟧ᴳ :=
  match Γ with
  | [] => Domain.const ()
  | _,' _ => Domain.comp₂ Domain.pair σ.tail.denot σ.head.denot
notation "⟦" σ "⟧ˢ" => Subst.denot σ

lemma Subst.denot_apply {σ : Subst Γ Δ} {x : T ∈' Γ} :
  ⟦σ x⟧ᵗ a = Con.denot_get x (⟦σ⟧ˢ a):= by
  induction' x with _ _ _ x ih <;> simp [Con.denot_get, Subst.denot]
  · simp [Subst.head]
  · have h := ih (σ := σ.tail)
    simp at h; rw [←h]
    simp [Subst.tail]

theorem Term.denot_subst {t : Term Γ T} {σ : Subst Γ Δ} :
  ⟦t[σ]ˢ⟧ᵗ = Domain.comp ⟦t⟧ᵗ ⟦σ⟧ˢ := by
  induction t generalizing Δ <;> simp [Term.subst, Term.denot]
  case var x => ext g; simp [Subst.denot_apply]
  case lam t ih =>
    ext g d
    simp [ih, Subst.denot]
    congr!
    apply Con.denot_ext
    intros T x
    simp [←Subst.denot_apply, Subst.tail, Subst.lift, Term.denot_shift]
  all_goals aesop

theorem Term.denot_subst_single {t₁ : Term (Γ,' T₁) T₂} :
  ⟦t₁[↦ t₂]ˢ⟧ᵗ = Domain.S (Domain.curry ⟦t₁⟧ᵗ) ⟦t₂⟧ᵗ := by
  ext g; simp [Term.denot_subst, Subst.denot]
  congr!
  simp [Subst.tail, Subst.single]
  apply Con.denot_ext
  intros T x
  simp [←Subst.denot_apply, Term.denot]

def Context.denot : Context Γ T Δ T' → (⟦Γ⟧ᴳ →ᴰ ⟦T⟧ᵀ) →ᴰ (⟦Δ⟧ᴳ →ᴰ ⟦T'⟧ᵀ)
| hole => Domain.I
| lam C => Domain.comp Domain.curry C.denot
| app₁ C t => Domain.comp ((Domain.swap Domain.S) ⟦t⟧ᵗ) C.denot
| app₂ t C => Domain.comp (Domain.S ⟦t⟧ᵗ) C.denot
| fix C => Domain.comp (Domain.comp Domain.fix) C.denot
| ite₁ C t₂ t₃ => Domain.comp (Domain.S (Domain.S (Domain.comp₃ Domain.ite) (Domain.K ⟦t₂⟧ᵗ)) (Domain.K ⟦t₃⟧ᵗ)) C.denot
| ite₂ t₁ C t₃ => Domain.comp (Domain.S (Domain.comp₃ Domain.ite ⟦t₁⟧ᵗ) (Domain.K ⟦t₃⟧ᵗ)) C.denot
| ite₃ t₁ t₂ C => Domain.comp (Domain.comp₃ Domain.ite ⟦t₁⟧ᵗ ⟦t₂⟧ᵗ) C.denot
| succ C => Domain.comp (Domain.comp Domain.succ) C.denot
| pred C => Domain.comp (Domain.comp Domain.pred) C.denot
| isz C => Domain.comp (Domain.comp Domain.isz) C.denot
| pair₁ C t => Domain.comp (Domain.comp₂ (Domain.swap Domain.pair) ⟦t⟧ᵗ) C.denot
| pair₂ t C => Domain.comp (Domain.comp₂ Domain.pair ⟦t⟧ᵗ) C.denot
| fst C => Domain.comp (Domain.comp Domain.fst) C.denot
| snd C => Domain.comp (Domain.comp Domain.snd) C.denot
notation "⟦" C "⟧ᶜ" => Context.denot C

theorem Context.denot_plug {C : Context Γ T Δ T'} :
  ⟦C.plug t⟧ᵗ = ⟦C⟧ᶜ ⟦t⟧ᵗ := by
  induction C <;> ext g <;>
    simp [Context.plug, Term.denot, Context.denot] <;> aesop

theorem compositionality {C : Context Γ T Δ T'} :
  ⟦t₁⟧ᵗ = ⟦t₂⟧ᵗ → ⟦C.plug t₁⟧ᵗ = ⟦C.plug t₂⟧ᵗ := by
  intro h
  simp [Context.denot_plug, h]

theorem Step.denot_eq : t₁ ⟶ t₂ → ⟦t₁⟧ᵗ = ⟦t₂⟧ᵗ := by
  intro h
  induction h <;> ext g <;> simp [Term.denot]
  case beta =>
    simp [Term.denot_subst_single]
  case fix₂ =>
    simp [Domain.fix_is_fixpoint]
  all_goals aesop

theorem Reduce.denot_eq : t₁ ⟶* t₂ → ⟦t₁⟧ᵗ = ⟦t₂⟧ᵗ := by
  intro h; induction h with
  | refl => rfl
  | step h _ ih => simp [ih, Step.denot_eq h]

theorem soundness : t₁ ≡ t₂ → ⟦t₁⟧ᵗ = ⟦t₂⟧ᵗ := by
  intro h; induction h with
  | refl => rfl
  | symm _ ih => simp [ih]
  | trans _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | step h => simp [Step.denot_eq h]

end PCF

end
