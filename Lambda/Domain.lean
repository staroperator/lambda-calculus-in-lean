-- import Std.Order.Basic
import Mathlib.Data.Set.Prod
import Mathlib.Order.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.ApplyAt

namespace Domain

lemma Monotone.prod_fst [PartialOrder α] [PartialOrder β] :
  Monotone (Prod.fst : α × β → α) := λ _ _ => And.left

lemma Monotone.prod_snd [PartialOrder α] [PartialOrder β] :
  Monotone (Prod.snd : α × β → β) := λ _ _ => And.right



def Directed [PartialOrder α] (s : Set α) : Prop :=
  s.Nonempty ∧ ∀ x ∈ s, ∀ y ∈ s, ∃ z ∈ s, x ≤ z ∧ y ≤ z

namespace Directed

variable [PartialOrder α] [PartialOrder β]

theorem singleton {x : α} : Directed {x} := by
  constructor
  · exists x
  · intros _ h₁ _ h₂
    cases h₁; cases h₂
    exists x

theorem prod {s : Set α} {t : Set β}
  (hs : Directed s) (ht : Directed t) : Directed (s ×ˢ t) := by
  constructor
  · rcases hs.1 with ⟨x, h₁⟩
    rcases ht.1 with ⟨y, h₂⟩
    exists ⟨x, y⟩
  · intro ⟨x₁, y₁⟩ ⟨h₁, h₁'⟩ ⟨x₂, y₂⟩ ⟨h₂, h₂'⟩
    rcases hs.2 _ h₁ _ h₂ with ⟨z₁, h₃, h₄, h₅⟩
    rcases ht.2 _ h₁' _ h₂' with ⟨z₂, h₃', h₄', h₅'⟩
    exists ⟨z₁, z₂⟩

theorem mono_image {f : α → β} {s : Set α}
  (hs : Directed s) (hf : Monotone f) : Directed (f '' s) := by
  constructor
  · rcases hs.1 with ⟨x, h⟩
    exists f x, x
  · intro _ ⟨x, ⟨h₁, h₁'⟩⟩ _ ⟨y, ⟨h₂, h₂'⟩⟩
    subst h₁' h₂'
    rcases hs.2 _ h₁ _ h₂ with ⟨z, _⟩
    exists f z, ⟨z, ?_⟩ <;> aesop

theorem prod_fst {s : Set (α × β)}
  (hs : Directed s) : Directed (Prod.fst '' s) :=
  mono_image hs Monotone.prod_fst

theorem prod_snd {s : Set (α × β)}
  (hs : Directed s) : Directed (Prod.snd '' s) :=
  mono_image hs Monotone.prod_snd

theorem mono_range {f : α → β}
  (hs : Directed (Set.univ : Set α)) (hf : Monotone f) :
  Directed (Set.range f) := by
  rw [←Set.image_univ]
  exact mono_image hs hf

theorem mono_comp_image {f : α → β} {s : Set ι} {g : ι → α}
  (hg : Directed (g '' s)) (hf : Monotone f) : Directed ((f ∘ g) '' s) := by
  constructor
  · rcases hg.1 with ⟨_, ⟨x, h, h'⟩⟩
    subst h'
    exists f (g x), x
  · intro _ ⟨x, h₁, h₁'⟩ _ ⟨y, h₂, h₂'⟩
    subst h₁' h₂'
    rcases hg.2 _ ⟨x, h₁, rfl⟩ _ ⟨y, h₂, rfl⟩ with ⟨_, ⟨z, _⟩, _⟩
    exists f (g z)
    aesop

theorem mono_comp_range {ι : Type w} {f : α → β} {g : ι → α}
  (hg : Directed (Set.range g)) (hf : Monotone f) : Directed (Set.range (f ∘ g)) := by
  rw [←Set.image_univ] at *
  exact mono_comp_image hg hf

end Directed

theorem Directed.linear_order [LinearOrder α] {s : Set α}
  (h : s.Nonempty) : Directed s := by
  constructor
  · exact h
  · intros x h₁ y h₂
    cases' le_total x y with h h
    · exists y
    · exists x

theorem Directed.linear_order_univ [LinearOrder α] [Nonempty α] :
  Directed (Set.univ : Set α) :=
  Directed.linear_order Set.univ_nonempty



class Dcpo (α : Type u) extends PartialOrder α where
  sSup : ∀ (s : Set α), Directed s → α
  sSup_is_lub : ∀ s hs, IsLUB s (@sSup s hs)

namespace Dcpo

variable [Dcpo α] [Dcpo β] [Dcpo γ]

theorem le_sSup {s : Set α} {hs} : x ∈ s → x ≤ sSup s hs := by
  intro h
  apply (Dcpo.sSup_is_lub s _).left
  exact h

theorem sSup_le {s : Set α} {hs} : (∀ y ∈ s, y ≤ x) → sSup s hs ≤ x := by
  intro h
  apply (Dcpo.sSup_is_lub s _).right
  exact h

def iSup (f : ι → α) (hf : Directed (Set.range f)) :=
  sSup (Set.range f) hf

theorem iSup.sSup {f : ι → α} {hf} : sSup (Set.range f) hf = iSup f hf := rfl

theorem le_iSup {f : ι → α} {hf} : f i ≤ iSup f hf := by
  apply le_sSup
  exists i

theorem iSup_le {f : ι → α} {hf} :
  (∀ i, f i ≤ a) → iSup f hf ≤ a := by
  intro h
  apply sSup_le
  intro _ ⟨i, h'⟩
  subst h'
  apply h

def iSupMem (s : Set ι) (f : ι → α) (hf : Directed (f '' s)) :=
  sSup (f '' s) hf

theorem iSupMem.sSup {f : ι → α} {hf} : sSup (f '' s) hf = iSupMem s f hf := rfl

theorem le_iSupMem {f : ι → α} {hf} :
  i ∈ s → f i ≤ iSupMem s f hf := by
  intro h
  apply Dcpo.le_sSup
  exists i

theorem iSupMem_le {f : ι → α} {hf} :
  (∀ i ∈ s, f i ≤ a) → iSupMem s f hf ≤ a := by
  intro h
  apply sSup_le
  intro _ ⟨i, h', h''⟩
  subst h''
  apply h
  exact h'

theorem iSupMem.comp {s : Set ι} {f : α → β} {g : ι → α} {hf} {hfg} :
  iSupMem (g '' s) f hf = iSupMem s (f ∘ g) hfg := by
  unfold iSupMem
  congr
  rw [Set.image_comp]

instance : Dcpo PUnit where
  sSup := λ s _ => ()
  sSup_is_lub := by
    intros _ _; constructor <;> intros _ _ <;> trivial

noncomputable def flat (α : Type u) : Dcpo α where
  le := λ x y => x = y
  le_refl := by intro; simp
  le_trans := by intros _ _ _ h₁ h₂; simp at *; simp [h₁, h₂]
  le_antisymm := by intros _ _ h₁ _; simp at *; exact h₁
  sSup := λ s hs => Classical.choose (by cases' hs with hs; exact hs)
  sSup_is_lub := by
    intro s hs
    cases' hs with hs₁ hs₂
    have h : ∀ x (_ : x ∈ s) (h' : s.Nonempty), Classical.choose h' = x := by
      intros x h h'
      let y := Classical.choose h'
      rcases hs₂ x h y (Classical.choose_spec h') with ⟨z, _, h₃, h₄⟩
      simp at *
      simp [h₃, h₄]
    constructor
    · intros y h₁
      simp [h y h₁]
    · cases' hs₁ with x h₁
      intros y h₂
      have h₃ := h₂ h₁
      simp at h₃
      simp [←h₃, h x h₁]

noncomputable instance lift : Dcpo (WithBot α) where
  sSup := λ s hs =>
    have := Classical.propDecidable
    if h : ∃ x, some x ∈ s then
      @Dcpo.sSup α _ { x | some x ∈ s } (by
        constructor
        · rcases h with ⟨x, h⟩
          exists x
        · intro x h₁ y h₂
          rcases hs.2 _ h₁ _ h₂ with ⟨z, h₃, h₄, h₅⟩
          cases' z with z
          · apply le_bot_iff.1 at h₄
            contradiction
          · simp at h₄ h₅
            exists z)
    else ⊥
  sSup_is_lub := by
    intros s hs
    by_cases h : ∃ x, some x ∈ s <;> simp [h]
    · constructor
      · intros x h₁ y h₂
        simp at h₂
        subst h₂
        refine ⟨_, rfl, ?_⟩
        apply le_sSup
        exact h₁
      · intros x h₁
        cases' x with x
        · cases' h with y h
          have h₂ := h₁ h
          apply le_bot_iff.1 at h₂
          contradiction
        · apply WithBot.some_le_some.2
          apply sSup_le
          intro y h₂
          apply h₁ at h₂
          simp at h₂
          exact h₂
    · constructor
      · intros x h₁ y h₂
        simp at h₂
        subst h₂
        exfalso
        apply h
        exists y
      · intros _ _
        simp

noncomputable def lift_flat (α : Type u) : Dcpo (WithBot α) := @Dcpo.lift _ (Dcpo.flat α)

instance prod : Dcpo (α × β) where
  sSup := λ s hs => ⟨
    iSupMem s Prod.fst (Directed.prod_fst hs),
    iSupMem s Prod.snd (Directed.prod_snd hs)⟩
  sSup_is_lub := by
    intros s _
    constructor
    · intro ⟨x, y⟩ _
      constructor <;> apply Dcpo.le_iSupMem <;> assumption
    · intro ⟨x, y⟩ h
      constructor <;> apply Dcpo.iSupMem_le <;>
        intro ⟨x, y⟩ h' <;> cases h h' <;> assumption

theorem prod.sSup {s : Set (α × β)} {hs} :
  sSup s hs = ⟨iSupMem s Prod.fst (Directed.prod_fst hs), iSupMem s Prod.snd (Directed.prod_snd hs)⟩ := rfl

theorem prod.iSupMem {s : Set ι} {f : ι → α × β} {hf} :
  iSupMem s f hf = ⟨iSupMem s (Prod.fst ∘ f) (Directed.mono_comp_image hf Monotone.prod_fst), iSupMem s (Prod.snd ∘ f) (Directed.mono_comp_image hf Monotone.prod_snd)⟩ := by
  trans
  · apply prod.sSup
  · congr <;> apply iSupMem.comp

theorem sSup_singleton {x : α} :
  sSup {x} Directed.singleton = x := by
  apply le_antisymm
  · apply sSup_le; simp
  · apply le_sSup; simp

end Dcpo



structure Continuous [Dcpo α] [Dcpo β] (f : α → β) : Prop where
  mono : Monotone f
  keeps_sSup : ∀ s hs, f (Dcpo.sSup s hs) = Dcpo.iSupMem s f (Directed.mono_image hs mono)

theorem Continuous.constant [Dcpo α] [Dcpo β] {b} : Continuous (λ _ => b : α → β) where
  mono := by
    intros _ _ _; apply le_refl
  keeps_sSup := by
    intros s hs
    apply le_antisymm
    · apply Dcpo.le_sSup
      rcases hs.1 with ⟨x, h⟩
      exists x
    · apply Dcpo.iSupMem_le
      intros
      apply le_refl

def ContinuousDomain (α β) [Dcpo α] [Dcpo β] := { f : α → β // Continuous f }
infix:min " →ᴰ " => ContinuousDomain

namespace ContinuousDomain

variable [Dcpo α] [Dcpo β]

instance : CoeFun (α →ᴰ β) (λ _ => α → β) := ⟨Subtype.val⟩

abbrev mono (f : α →ᴰ β) := f.property.mono
abbrev keeps_sSup (f : α →ᴰ β) := f.property.keeps_sSup

theorem keeps_iSup (f : α →ᴰ β) {g : ι → α} {hg} :
  f (Dcpo.iSup g hg) = Dcpo.iSup (f ∘ g) (Directed.mono_comp_range hg f.mono) := by
  unfold Dcpo.iSup
  rw [f.keeps_sSup]
  unfold Dcpo.iSupMem
  congr
  ext _
  constructor
  · intro ⟨_, ⟨i, h⟩, h'⟩
    subst h h'
    exists i
  · intro ⟨i, h⟩
    subst h
    exists g i
    aesop

theorem keeps_iSupMem (f : α →ᴰ β) {s : Set ι} {g : ι → α} {hg} :
  f (Dcpo.iSupMem s g hg) = Dcpo.iSupMem s (f ∘ g) (Directed.mono_comp_image hg f.mono) := by
  unfold Dcpo.iSupMem
  rw [f.keeps_sSup]
  unfold Dcpo.iSupMem
  congr
  ext _
  constructor
  · intro ⟨_, ⟨i, h, h'⟩, h''⟩
    subst h' h''
    exists i
  · intro ⟨i, h, h'⟩
    subst h'
    exists g i
    aesop

end ContinuousDomain

section

variable [Dcpo α] [Dcpo β] [Dcpo γ]

instance : PartialOrder (α →ᴰ β) := by
  unfold ContinuousDomain
  exact inferInstance

lemma Monotone.apply {x : α} : Monotone (λ (f : α →ᴰ β) => f x) :=
  λ _ _ h => h x

lemma Directed.pointwise {s : Set (α →ᴰ β)} (hs : Directed s) :
  Directed ((λ f => f x) '' s) :=
  Directed.mono_image hs Monotone.apply

instance Dcpo.continuous : Dcpo (α →ᴰ β) where
  sSup := λ s hs => ⟨
    λ x => Dcpo.iSupMem s (λ f => f x) (Directed.pointwise hs),
    { mono := by
        intros x y h
        apply iSupMem_le
        intros f h₁
        apply le_trans (f.mono h)
        apply le_iSupMem h₁
      keeps_sSup := by
        intros s' hs'
        apply le_antisymm
        · apply iSupMem_le
          intros f h₁
          rw [f.keeps_sSup]
          apply iSupMem_le
          intros x h₂
          apply le_trans'
          · exact le_iSupMem h₂
          · apply le_iSupMem h₁
        · apply iSupMem_le
          intros x h₁
          apply iSupMem_le
          intros f h₂
          apply le_trans'
          · apply le_iSupMem h₂
          · apply f.mono
            exact le_sSup h₁ }⟩
  sSup_is_lub := by
    intros s hs
    constructor
    · intros f h x
      apply le_iSupMem h
    · intros f h x
      apply iSupMem_le
      intros g h₁
      apply h
      exact h₁

theorem Dcpo.continuous.sSup {s : Set (α →ᴰ β)} {hs} :
  (sSup s hs) x = iSupMem s (λ f => f x) (Directed.pointwise hs) := rfl

theorem Dcpo.continuous.iSupMem {s : Set ι} {f : ι → (α →ᴰ β)} {hf} :
  (iSupMem s f hf) x = iSupMem s (λ i => f i x) (Directed.mono_comp_image hf Monotone.apply) := by
  trans
  · apply sSup
  · apply iSupMem.comp



def fst : α × β →ᴰ α where
  val := Prod.fst
  property := {
    mono := λ _ _ ⟨h, _⟩ => h
    keeps_sSup := λ _ _ => rfl
  }

def snd : α × β →ᴰ β where
  val := Prod.snd
  property := {
    mono := λ _ _ ⟨_, h⟩ => h
    keeps_sSup := λ _ _ => rfl
  }

def apply : (α →ᴰ β) × α →ᴰ β where
  val := λ ⟨f, x⟩ => f x
  property := {
    mono := by
      intro ⟨f, x⟩ ⟨g, y⟩ ⟨h₁, h₂⟩
      simp at *
      apply le_trans
      · apply f.mono; exact h₂
      · apply h₁
    keeps_sSup := by
      intros s hs
      simp [Dcpo.continuous.iSupMem, Dcpo.prod.iSupMem]
      apply le_antisymm
      · apply Dcpo.iSupMem_le
        intro ⟨f, x⟩ h₁
        simp
        rw [f.keeps_iSupMem]
        apply Dcpo.iSupMem_le
        intro ⟨g, y⟩ h₂
        rcases hs.2 _ h₁ _ h₂ with ⟨⟨h, z⟩, h₃, h₄, h₅⟩
        simp at *
        apply le_trans (f.mono h₅.2)
        apply le_trans (h₄.1 z)
        exact Dcpo.le_iSupMem (f := λ ⟨f, x⟩ => f x) h₃
      · apply Dcpo.iSupMem_le
        intro ⟨f, x⟩ h₁
        apply le_trans'
        · apply Dcpo.le_iSupMem h₁
        · apply f.mono
          apply Dcpo.le_iSupMem h₁
  }

def curry (f : α × β →ᴰ γ) : (α →ᴰ (β →ᴰ γ)) where
  val := λ x => {
    val := λ y => f ⟨x, y⟩
    property := {
      mono := by
        intros y₁ y₂ h
        apply f.mono
        exact ⟨le_refl _, h⟩
      keeps_sSup := by
        intros s hs
        trans f (Dcpo.iSupMem s (λ y => ⟨x, y⟩) (Directed.mono_image hs (λ _ _ => And.intro (le_refl _))))
        · apply congr_arg
          rw [Dcpo.prod.iSupMem]
          congr
          · unfold Dcpo.iSupMem
            conv => lhs; rw [←Dcpo.sSup_singleton (x := x)]
            congr
            ext _
            constructor
            · rcases hs.1 with ⟨y, h⟩
              aesop
            · aesop
          · ext _
            aesop
        · rw [f.keeps_iSupMem]
          rfl
    }
  }
  property := {
    mono := by
      intro x₁ x₂ h y
      apply f.mono
      exact ⟨h, le_refl _⟩
    keeps_sSup := by
      intros s hs
      congr
      funext y
      trans f (Dcpo.iSupMem s (λ x => ⟨x, y⟩) (Directed.mono_image hs (λ _ _ => (And.intro . (le_refl _)))))
      · apply congr_arg
        rw [Dcpo.prod.iSupMem]
        congr
        · ext _
          aesop
        · unfold Dcpo.iSupMem
          conv => lhs; rw [←Dcpo.sSup_singleton (x := y)]
          congr
          ext _
          constructor
          · rcases hs.1 with ⟨y, h⟩
            aesop
          · aesop
      · rw [f.keeps_iSupMem]
        unfold Dcpo.iSupMem
        congr
        ext _
        constructor
        · intro ⟨x, h₁, h₁'⟩
          subst h₁'
          simp
          exists x
        · intro ⟨_, ⟨x, h₁, h₁'⟩, h₁''⟩
          subst h₁' h₁''
          simp
          exists x
  }

def uncurry (f : α →ᴰ (β →ᴰ γ)) : α × β →ᴰ γ where
  val := λ ⟨x, y⟩ => f x y
  property := {
    mono := by
      intro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ⟨h₁, h₂⟩
      simp at *
      trans
      · exact (f x₁).mono h₂
      · apply f.mono h₁
    keeps_sSup := by
      intros s hs
      simp [f.keeps_iSupMem, Dcpo.continuous.iSupMem]
      apply le_antisymm
      · apply Dcpo.iSupMem_le
        intro ⟨x₁, y₁⟩ h₁
        rw [(f x₁).keeps_iSupMem]
        apply Dcpo.iSupMem_le
        intro ⟨x₂, y₂⟩ h₂
        rcases hs.2 _ h₁ _ h₂ with ⟨⟨x₃, y₃⟩, h₃, h₄, h₅⟩
        apply le_trans (f.mono h₄.1 _)
        apply le_trans ((f x₃).mono h₅.2)
        exact Dcpo.le_iSupMem (f := λ ⟨x, y⟩ => f x y) h₃
      · apply Dcpo.iSupMem_le
        intro ⟨x, y⟩ h
        apply le_trans' (Dcpo.le_iSupMem h)
        apply (f x).mono
        exact Dcpo.le_iSupMem h
  }

end



class DcpoBot (α : Type u) extends Dcpo α, OrderBot α

noncomputable instance [Dcpo α] : DcpoBot (WithBot α) where
noncomputable def DcpoBot.lift_flat (α : Type u) : DcpoBot (WithBot α) :=
  @DcpoBot.mk _ (Dcpo.lift_flat α) inferInstance

instance : DcpoBot PUnit where
instance [DcpoBot α] [DcpoBot β] : DcpoBot (α × β) where

instance DcpoBot.continuous [Dcpo α] [DcpoBot β] : DcpoBot (α →ᴰ β) where
  bot := ⟨λ _ => ⊥, Continuous.constant⟩
  bot_le := by intro f x; apply bot_le

namespace ContinuousDomain

theorem bot_iff [Dcpo α] [DcpoBot β] {f : α →ᴰ β} :
  f = ⊥ ↔ ∀ x, f x = ⊥ := by
  constructor
  · intro h; subst h; aesop
  · intro h
    cases f
    simp [Bot.bot]
    congr
    funext; apply h

variable [DcpoBot α] (f : α →ᴰ α)

def iter : Nat → α
| 0 => ⊥
| n + 1 => f (iter n)

lemma iter_mono : Monotone (iter f) := by
  intro n m h
  induction' h with m h ih
  · apply le_refl
  · apply le_trans ih
    clear h ih
    induction' m with m ih
    · apply bot_le
    · apply f.mono
      exact ih

def fix : α :=
  Dcpo.iSup (iter f) (Directed.mono_range Directed.linear_order_univ (iter_mono f))

theorem fix_is_fixpoint : f (fix f) = fix f := by
  unfold fix
  rw [f.keeps_iSup]
  apply le_antisymm
  · apply Dcpo.iSup_le
    intro n
    simp
    rw [←iter]
    apply Dcpo.le_iSup
  · apply Dcpo.iSup_le
    intro n
    apply le_trans' (Dcpo.le_iSup (i := n))
    simp
    rw [←iter]
    apply iter_mono
    apply Nat.le_succ

theorem fix_is_least_fixpoint : f x = x → fix f ≤ x := by
  intro h
  apply Dcpo.iSup_le
  intro n
  induction' n with n ih
  · apply bot_le
  · unfold iter
    rw [←h]
    apply f.mono
    exact ih

end ContinuousDomain
