import Mathlib.Data.Set.Prod
import Mathlib.Order.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Bounds.Basic
import Lambda.Prelude

lemma Set.comp_image {f : β → γ} {g : α → β} {s : Set α} : f '' (g '' s) = f ∘ g '' s := by
  ext x; constructor
  · intro ⟨_, ⟨x, _, h⟩, h'⟩; subst h h'; exists x
  · intro ⟨x, h, h'⟩; subst h'; exists g x, ⟨x, h, rfl⟩ 

namespace Monotone

variable [PartialOrder α] [PartialOrder β]

lemma prod_fst : Monotone (Prod.fst : α × β → α) :=
  λ _ _ => And.left

lemma prod_snd : Monotone (Prod.snd : α × β → β) :=
  λ _ _ => And.right

end Monotone


def Directed' [PartialOrder α] (s : Set α) : Prop :=
  s.Nonempty ∧ ∀ x ∈ s, ∀ y ∈ s, ∃ z ∈ s, x ≤ z ∧ y ≤ z

namespace Directed'

variable [PartialOrder α] [PartialOrder β]

theorem singleton {x : α} : Directed' {x} := by
  constructor
  · exists x
  · intros _ h₁ _ h₂
    cases h₁; cases h₂
    exists x

theorem pair {x y : α} : x ≤ y → Directed' {x, y} := by
  intro h
  constructor
  · exists x; aesop
  · intros _ h₁ _ h₂
    exists y; aesop

theorem prod {s : Set α} {t : Set β}
  (hs : Directed' s) (ht : Directed' t) : Directed' (s ×ˢ t) := by
  constructor
  · rcases hs.1 with ⟨x, h₁⟩
    rcases ht.1 with ⟨y, h₂⟩
    exists ⟨x, y⟩
  · intro ⟨x₁, y₁⟩ ⟨h₁, h₁'⟩ ⟨x₂, y₂⟩ ⟨h₂, h₂'⟩
    rcases hs.2 _ h₁ _ h₂ with ⟨z₁, h₃, h₄, h₅⟩
    rcases ht.2 _ h₁' _ h₂' with ⟨z₂, h₃', h₄', h₅'⟩
    exists ⟨z₁, z₂⟩

theorem mono_image {f : α → β} {s : Set α}
  (hs : Directed' s) (hf : Monotone f) : Directed' (f '' s) := by
  constructor
  · rcases hs.1 with ⟨x, h⟩
    exists f x, x
  · intro _ ⟨x, ⟨h₁, h₁'⟩⟩ _ ⟨y, ⟨h₂, h₂'⟩⟩
    subst h₁' h₂'
    rcases hs.2 _ h₁ _ h₂ with ⟨z, _⟩
    exists f z, ⟨z, ?_⟩ <;> aesop

theorem prod_fst {s : Set (α × β)}
  (hs : Directed' s) : Directed' (Prod.fst '' s) :=
  mono_image hs Monotone.prod_fst

theorem prod_snd {s : Set (α × β)}
  (hs : Directed' s) : Directed' (Prod.snd '' s) :=
  mono_image hs Monotone.prod_snd

theorem mono_range {f : α → β}
  (hs : Directed' (Set.univ : Set α)) (hf : Monotone f) :
  Directed' (Set.range f) := by
  rw [←Set.image_univ]
  exact mono_image hs hf

theorem mono_comp_image {f : α → β} {s : Set ι} {g : ι → α}
  (hg : Directed' (g '' s)) (hf : Monotone f) : Directed' ((f ∘ g) '' s) := by
  constructor
  · rcases hg.1 with ⟨_, ⟨x, h, h'⟩⟩
    subst h'
    exists f (g x), x
  · intro _ ⟨x, h₁, h₁'⟩ _ ⟨y, h₂, h₂'⟩
    subst h₁' h₂'
    rcases hg.2 _ ⟨x, h₁, rfl⟩ _ ⟨y, h₂, rfl⟩ with ⟨_, ⟨z, _⟩, _⟩
    exists f (g z)
    aesop

theorem mono_comp_range {ι : Type u} {f : α → β} {g : ι → α}
  (hg : Directed' (Set.range g)) (hf : Monotone f) : Directed' (Set.range (f ∘ g)) := by
  rw [←Set.image_univ] at *
  exact mono_comp_image hg hf

end Directed'

theorem Directed'.linear_order [LinearOrder α] {s : Set α}
  (h : s.Nonempty) : Directed' s := by
  constructor
  · exact h
  · intros x h₁ y h₂
    cases' le_total x y with h h
    · exists y
    · exists x

theorem Directed'.linear_order_univ [LinearOrder α] [Nonempty α] :
  Directed' (Set.univ : Set α) :=
  Directed'.linear_order Set.univ_nonempty



class Dcpo (α : Type u) extends PartialOrder α where
  sSup : ∀ (s : Set α), Directed' s → α
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

def iSup (f : ι → α) (hf : Directed' (Set.range f)) :=
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

theorem iSup.mono {f g : ι → α} {hf hg} :
  (∀ i, f i ≤ g i) → iSup f hf ≤ iSup g hg := by
  intro h
  apply iSup_le
  intro i
  apply le_trans (h i)
  exact le_iSup

def iSupMem (s : Set ι) (f : ι → α) (hf : Directed' (f '' s)) :=
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

theorem iSupMem.comp {s : Set ι} {f : α → β} {g : ι → α} {hf} :
  iSupMem (g '' s) f hf = iSupMem s (f ∘ g) (by rw [←Set.comp_image]; exact hf) := by
  unfold iSupMem
  congr
  rw [Set.comp_image]

theorem iSupMem.mono {s : Set ι} {f g : ι → α} {hf} {hg} :
  (∀ i ∈ s, f i ≤ g i) → iSupMem s f hf ≤ iSupMem s g hg := by
  intro h
  apply iSupMem_le
  intros i h'
  apply le_trans (h i h')
  exact le_iSupMem h'

theorem sSup.singleton {x : α} :
  sSup {x} Directed'.singleton = x := by
  apply le_antisymm
  · apply sSup_le; simp
  · apply le_sSup; simp

theorem sSup.pair {x y : α} (h : x ≤ y) :
  sSup {x, y} (Directed'.pair h) = y := by
  apply le_antisymm
  · apply sSup_le; simp; exact h
  · apply le_sSup; simp

end Dcpo

structure Continuous [Dcpo α] [Dcpo β] (f : α → β) : Prop where
  mono : Monotone f
  keeps_sSup : ∀ s hs, f (Dcpo.sSup s hs) = Dcpo.iSupMem s f (Directed'.mono_image hs mono)

namespace Continuous

variable [Dcpo α] [Dcpo β] {f : α → β} (hf : Continuous f)

theorem keeps_iSup {g : ι → α} {hg} :
  f (Dcpo.iSup g hg) = Dcpo.iSup (f ∘ g) (Directed'.mono_comp_range hg hf.mono) := by
  unfold Dcpo.iSup
  rw [hf.keeps_sSup]
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

theorem keeps_iSupMem {s : Set ι} {g : ι → α} {hg} :
  f (Dcpo.iSupMem s g hg) = Dcpo.iSupMem s (f ∘ g) (Directed'.mono_comp_image hg hf.mono) := by
  unfold Dcpo.iSupMem
  rw [hf.keeps_sSup]
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

theorem const {b} : Continuous (λ _ => b : α → β) where
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

end Continuous



structure Domain where
  carrier : Type u
  dcpo : Dcpo carrier
  orderBot : OrderBot carrier

instance : CoeSort Domain.{u} (Type u) := ⟨Domain.carrier⟩
instance {α : Domain} : Dcpo α := α.dcpo
instance {α : Domain} : OrderBot α := α.orderBot

namespace Domain

variable {α β γ : Domain}

def Unit : Domain where
  carrier := PUnit
  dcpo := {
    sSup := λ s _ => ()
    sSup_is_lub := by
      intros _ _; constructor <;> intros _ _ <;> trivial
  }
  orderBot := inferInstance

def Prod (α β : Domain) : Domain where
  carrier := α × β
  dcpo := {
    sSup := λ s hs => ⟨
      Dcpo.iSupMem s Prod.fst (Directed'.prod_fst hs),
      Dcpo.iSupMem s Prod.snd (Directed'.prod_snd hs)⟩
    sSup_is_lub := by
      intros s _
      constructor
      · intro ⟨x, y⟩ _
        constructor <;> apply Dcpo.le_iSupMem <;> assumption
      · intro ⟨x, y⟩ h
        constructor <;> apply Dcpo.iSupMem_le <;>
          intro ⟨x, y⟩ h' <;> cases h h' <;> assumption
  }
  orderBot := inferInstance

infixr:35 " ×ᴰ " => Prod

theorem Prod.sSup {s : Set (α ×ᴰ β)} {hs} :
  Dcpo.sSup s hs = ⟨
    Dcpo.iSupMem s Prod.fst (Directed'.prod_fst hs),
    Dcpo.iSupMem s Prod.snd (Directed'.prod_snd hs)
  ⟩ := rfl

theorem Prod.iSupMem {s : Set ι} {f : ι → α ×ᴰ β} {hf} :
  Dcpo.iSupMem s f hf = ⟨
    Dcpo.iSupMem s (Prod.fst ∘ f) (Directed'.mono_comp_image hf Monotone.prod_fst),
    Dcpo.iSupMem s (Prod.snd ∘ f) (Directed'.mono_comp_image hf Monotone.prod_snd)
  ⟩ := by
  trans
  · apply sSup
  · congr <;> apply Dcpo.iSupMem.comp

noncomputable def Flat (α : Type u) : Domain :=
  let instLE : LE (Option α) := {
    le := λ
          | some x, some y => x = y
          | some _, none => False
          | none, _ => True }
  { carrier := Option α
    dcpo := {
      le_refl := by intro x; cases x <;> simp
      le_trans := by
        intros x y z h₁ h₂
        cases x <;> cases y <;> cases z <;> simp at *
        simp [h₁, h₂]
      le_antisymm := by
        intros x y h _
        cases x <;> cases y <;> simp at *;
        simp [h]
      sSup := λ s _ =>
        have := Classical.propDecidable
        if h : ∃ x, some x ∈ s then
          some (Classical.choose h)
        else none
      sSup_is_lub := by
        intros s hs
        by_cases h : ∃ x, some x ∈ s <;> simp [h]
        · have hlemma : ∀ x (_ : some x ∈ s)
            (h' : ∃ x, some x ∈ s), Classical.choose h' = x := by
            intros x h h'
            let y := Classical.choose h'
            rcases hs.2 x h y (Classical.choose_spec h') with ⟨z, _, h₃, h₄⟩
            cases z <;> simp at *
            simp [h₃, h₄]
          constructor
          · intros x h₁; cases x <;> simp
            simp [hlemma _ h₁]
          · intros _ h₁
            apply h₁
            apply Classical.choose_spec (p := λ x => some x ∈ s)
        · constructor
          · intros x h₁
            cases x <;> simp
            exact h ⟨_, h₁⟩
          · intros _ _; simp
    }
    orderBot := {
      bot := none
      bot_le := by intro; simp
    }
  }

namespace Flat

variable {α : Type u} {x y : α} {s : Set (Flat α)}

lemma directed_some_unique (hs : Directed' s) :
  some x ∈ s → some y ∈ s → x = y := by
  intro h₁ h₂
  rcases hs.2 _ h₁ _ h₂ with ⟨z, h₃, h₄, h₅⟩
  cases z
  · contradiction
  · exact Eq.trans h₄ (symm h₅)

lemma directed_cases (hs : Directed' s) :
  (s = {⊥} ∨ (∃ x, s = {some x}) ∨ ∃ x, s = {⊥, some x}) := by
  by_cases h₁ : ⊥ ∈ s
  · by_cases h₂ : ∃ x, some x ∈ s
    · cases' h₂ with x h₂
      right; right; exists x
      ext y; constructor
      · intro h₃; cases y
        · left; rfl
        · right; congr; exact directed_some_unique hs h₃ h₂
      · intro h₃; cases h₃ <;> aesop
    · left; ext x; constructor
      · intro h; cases x
        · rfl
        · exfalso; apply h₂; exact ⟨_, h⟩
      · aesop
  · right; left
    rcases hs.1 with ⟨x, h₂⟩
    cases' x with x
    · contradiction
    · exists x; ext y; constructor
      · intro h; cases y
        · contradiction
        · congr; exact directed_some_unique hs h h₂
      · aesop

theorem sSup_eq_some {hs} :
  Dcpo.sSup s hs = some x → s = {some x} ∨ s = {⊥, some x} := by
  intro h
  rcases directed_cases hs with h₁ | h₁ | h₁
  · exfalso; subst h₁
    simp [Dcpo.sSup.singleton] at h
    contradiction
  · left; cases' h₁ with y h₁; subst h₁
    simp [Dcpo.sSup.singleton] at h
    simp [h]
  · right; cases' h₁ with y h₁; subst h₁
    simp [Dcpo.sSup.pair bot_le] at h
    simp [h]

theorem sSup_eq_none {hs} :
  Dcpo.sSup s hs = none → s = {⊥} := by
  intro h
  rcases directed_cases hs with h₁ | h₁ | h₁
  · exact h₁
  · cases' h₁ with y h₁; subst h₁
    simp [Dcpo.sSup.singleton] at h
  · cases' h₁ with y h₁; subst h₁
    simp [Dcpo.sSup.pair bot_le] at h

end Flat

def ContinuousMap (α β : Domain) : Domain where
  carrier :=
    { f : α → β // Continuous f }
  dcpo := {
    sSup := λ s hs => {
      val := λ x =>
        Dcpo.iSupMem s (λ f => f.val x) (by
          apply Directed'.mono_image hs
          intros _ _ h
          apply h)
      property := {
        mono := by
          intros x y h
          apply Dcpo.iSupMem.mono
          intros f _
          exact f.2.mono h
        keeps_sSup := by
          intros s' hs'
          apply le_antisymm
          · apply Dcpo.iSupMem_le
            intros f h₁
            rw [f.2.keeps_sSup]
            apply Dcpo.iSupMem.mono
            intros x _
            apply Dcpo.le_iSupMem h₁
          · apply Dcpo.iSupMem_le
            intros x h₁
            apply Dcpo.iSupMem_le
            intros f h₂
            apply le_trans'
            · apply Dcpo.le_iSupMem h₂
            · apply f.2.mono
              exact Dcpo.le_sSup h₁
        }
      }
    sSup_is_lub := by
      intros s hs
      constructor
      · intros f h x
        apply Dcpo.le_iSupMem h
      · intros f h x
        apply Dcpo.iSupMem_le
        intros g h₁
        apply h
        exact h₁
  }
  orderBot := {
    bot := {
      val := λ _ => ⊥
      property := Continuous.const
    }
    bot_le := by intro _ _; apply bot_le
  }
infixr:25 " →ᴰ " => ContinuousMap
instance : CoeFun (α →ᴰ β) (λ _ => α → β) :=
  ⟨Subtype.val⟩

@[simp] theorem ContinuousMap.bot_apply :
  (⊥ : α →ᴰ β) x = ⊥ := rfl

@[ext] theorem ContinuousMap.ext {f g : α →ᴰ β} :
  (∀ x, f x = g x) → f = g := by
  intro h; cases f; cases g; congr; ext; apply h

theorem ContinuousMap.bot_iff {f : α →ᴰ β} :
  f = ⊥ ↔ ∀ x, f x = ⊥ := by
  constructor
  · intro h; subst h; aesop
  · intro h; cases f; congr; funext; apply h

lemma _root_.Monotone.apply :
  Monotone (λ (f : α →ᴰ β) => f x) := by
  intros _ _ h; simp; apply h

lemma _root_.Directed'.pointwise {s : Set (α →ᴰ β)}
  (hs : Directed' s) : Directed' ((λ f => f x) '' s) :=
  Directed'.mono_image hs Monotone.apply

theorem ContinuousMap.sSup {s : Set (α →ᴰ β)} {hs} :
  (Dcpo.sSup s hs) x = Dcpo.iSupMem s (λ f => f x) (Directed'.pointwise hs) := rfl

theorem ContinuousMap.iSupMem {s : Set ι} {f : ι → α →ᴰ β} {hf} :
  (Dcpo.iSupMem s f hf) x = Dcpo.iSupMem s (λ i => f i x) (Directed'.mono_comp_image hf Monotone.apply) := by
  trans
  · apply sSup
  · apply Dcpo.iSupMem.comp

def pair : α →ᴰ β →ᴰ α ×ᴰ β where
  val := λ x => {
    val := λ y => ⟨x, y⟩
    property := {
      mono := λ y₁ y₂ h => ⟨le_refl _, h⟩,
      keeps_sSup := by
        intro s hs
        simp [Prod.iSupMem]
        congr
        · conv => lhs; rw [←Dcpo.sSup.singleton (x := x)]
          congr; ext _; constructor
          · intro h; cases h; simp; exact hs.1
          · intro ⟨y, _, h⟩; subst h; rfl
        · ext x'; constructor
          · intro h; exists x'
          · intro ⟨x'', h, h'⟩; subst h'; exact h
    }
  }
  property := {
    mono := λ x₁ x₂ h y => ⟨h, le_refl _⟩
    keeps_sSup := by
      intro s hs
      congr; funext y; simp [Prod.iSupMem]
      constructor
      · congr; ext x; simp
      · conv => lhs; rw [←Dcpo.sSup.singleton (x := y)]
        congr; ext _; constructor
        · intro h; cases h; simp; exact hs.1
        · intro ⟨f, ⟨x, _, h⟩, h'⟩; subst h h'; simp
  }
@[simp] theorem pair.apply : pair x y = ⟨x, y⟩ := rfl

def fst : α ×ᴰ β →ᴰ α where
  val := Prod.fst
  property := {
    mono := λ _ _ ⟨h, _⟩ => h
    keeps_sSup := λ _ _ => rfl
  }
@[simp] theorem fst.apply : fst ⟨x, y⟩ = x := rfl

def snd : α ×ᴰ β →ᴰ β where
  val := Prod.snd
  property := {
    mono := λ _ _ ⟨_, h⟩ => h
    keeps_sSup := λ _ _ => rfl
  }
@[simp] theorem snd.apply : snd ⟨x, y⟩ = y := rfl

def I : α →ᴰ α  where
  val := λ x => x
  property := {
    mono := by intros _ _ h; exact h
    keeps_sSup := by intros s hs; simp [Dcpo.iSupMem]
  }
@[simp] theorem I.apply : I x = x := rfl

def K : α →ᴰ β →ᴰ α where
  val := λ x => {
    val := λ _ => x
    property := {
      mono := λ _ _ _ => le_refl _
      keeps_sSup := by
        intro s hs
        conv => lhs; rw [←Dcpo.sSup.singleton (x := x)]
        congr; ext x'; constructor
        · intro h; cases h; simp; exact hs.1
        · intro ⟨x', _, h⟩; subst h; rfl
    }
  }
  property := {
    mono := λ _ _ h _ => h
    keeps_sSup := by
      intro s hs
      ext y; simp [ContinuousMap.iSupMem]
      congr; ext x; constructor <;> simp
  }
@[simp] theorem K.apply : K x y = x := rfl

def S : (α →ᴰ β →ᴰ γ) →ᴰ (α →ᴰ β) →ᴰ α →ᴰ γ where
  val := λ f => {
    val := λ g => {
      val := λ x => f x (g x)
      property := {
        mono := by
          intros x y h
          trans
          · apply f.2.mono h
          · apply (f y).2.mono; exact g.2.mono h
        keeps_sSup := by
          intros s hs
          simp [f.2.keeps_sSup, g.2.keeps_sSup, ContinuousMap.iSupMem]
          trans Dcpo.iSupMem s
            (λ x => Dcpo.iSupMem s (λ y => f x (g y))
              (Directed'.mono_image hs (λ _ _ h => (f x).2.mono (g.2.mono h))))
            (Directed'.mono_image hs (λ _ _ h => Dcpo.iSupMem.mono
              (λ _ _ => f.2.mono h _)))
          · congr; ext x; apply (f x).2.keeps_iSupMem
          · apply le_antisymm
            · apply Dcpo.iSupMem_le
              intros x h₁
              apply Dcpo.iSupMem_le
              intros y h₂
              rcases hs.2 _ h₁ _ h₂ with ⟨z, h₃, h₄, h₅⟩
              apply le_trans (f.2.mono h₄ _)
              apply le_trans ((f z).2.mono (g.2.mono h₅))
              apply Dcpo.le_iSupMem h₃
            · apply Dcpo.iSupMem_le
              intros x h₁
              apply le_trans' (Dcpo.le_iSupMem h₁)
              exact Dcpo.le_iSupMem (f := λ y => f x (g y)) h₁
      }
    }
    property := {
      mono := λ g₁ g₂ h x => (f x).2.mono (h x)
      keeps_sSup := by
        intro s hs
        congr; ext x
        simp [ContinuousMap.sSup]
        rw [(f x).2.keeps_iSupMem, Dcpo.iSupMem.comp]
        congr
    }
  }
  property := {
    mono := λ f₁ f₂ h g x => h x (g x)
    keeps_sSup := by
      intros s hs
      congr; ext g x
      simp [ContinuousMap.sSup, ContinuousMap.iSupMem]
      rw [Dcpo.iSupMem.comp]
      congr
  }
@[simp] theorem S.apply : S f g x = f x (g x) := rfl

def const {α β : Domain} (b : β) : α →ᴰ β := K b
@[simp] theorem const.apply : const b x = b := rfl

def comp : (β →ᴰ γ) →ᴰ (α →ᴰ β) →ᴰ α →ᴰ γ :=
  S (K S) K
@[simp] theorem comp.apply : comp f g x = f (g x) := rfl

def comp₂ : (β₁ →ᴰ β₂ →ᴰ γ) →ᴰ (α →ᴰ β₁) →ᴰ (α →ᴰ β₂) →ᴰ (α →ᴰ γ) :=
  S (K (S (K S))) (S (K S) K)
@[simp] theorem comp₂.apply : comp₂ f g₁ g₂ x = f (g₁ x) (g₂ x) := rfl

def comp₃ : (β₁ →ᴰ β₂ →ᴰ β₃ →ᴰ γ) →ᴰ (α →ᴰ β₁) →ᴰ (α →ᴰ β₂) →ᴰ (α →ᴰ β₃) →ᴰ (α →ᴰ γ) :=
  S (K (S (K (S (K S))))) (S (K (S (K S))) (S (K S) K))
@[simp] theorem comp₃.apply : comp₃ f g₁ g₂ g₃ x = f (g₁ x) (g₂ x) (g₃ x) := rfl

def swap : (α →ᴰ β →ᴰ γ) →ᴰ β →ᴰ α →ᴰ γ :=
  S (S (K (S (K S) K)) S) (K K)
@[simp] theorem swap.apply : swap f x y = f y x := rfl

def apply : (α →ᴰ β) ×ᴰ α →ᴰ β :=
  S fst snd
@[simp] theorem apply.apply : apply ⟨f, x⟩ = f x := rfl

def curry : (α ×ᴰ β →ᴰ γ) →ᴰ (α →ᴰ β →ᴰ γ) :=
  S (S (K S) (S (K K) (S (K S) K))) (K pair)
@[simp] theorem curry.apply : curry f x y = f ⟨x, y⟩ := rfl

def uncurry : (α →ᴰ (β →ᴰ γ)) →ᴰ α ×ᴰ β →ᴰ γ :=
  S (S (K S) (S (S (K S) K) (K fst))) (K snd)
@[simp] theorem uncurry.apply : uncurry f ⟨x, y⟩ = f x y := rfl

def curry₂ : (α ×ᴰ β ×ᴰ γ →ᴰ δ) →ᴰ α →ᴰ β →ᴰ γ →ᴰ δ :=
  S (S (K S) (S (K K) (S (K S) (S (K K) (S (K S) K)))))
    (K (S (S (K S) (S (K K) (S (K S) (S (K K) pair)))) (K pair)))
@[simp] theorem curry₂.apply : curry₂ f x y z = f ⟨x, y, z⟩ := rfl



def iter (f : α →ᴰ α) : Nat → α
| 0 => ⊥
| n + 1 => f (iter f n)

lemma iter_mono : Monotone (iter f) := by
  intro n m h
  induction' h with m h ih
  · apply le_refl
  · apply le_trans ih
    clear h ih
    induction' m with m ih
    · apply bot_le
    · apply f.2.mono
      exact ih

lemma iter_mono' : Monotone (λ (f : α →ᴰ α) => iter f n) := by
  intros f g h
  induction' n with n ih
  · apply le_refl
  · apply le_trans (f.2.mono ih)
    apply h

def fix : (α →ᴰ α) →ᴰ α where
  val := λ f => Dcpo.iSup (iter f) (Directed'.mono_range Directed'.linear_order_univ iter_mono)
  property := {
    mono := by
      intros f g h
      apply Dcpo.iSup.mono
      intro n
      apply iter_mono' h
    keeps_sSup := by
      intros s hs
      apply le_antisymm
      · apply Dcpo.iSup_le
        intro n
        induction' n with n ih
        · apply bot_le
        · simp [iter, ContinuousMap.sSup]
          apply Dcpo.iSupMem_le
          intro f h₁
          apply le_trans (f.2.mono ih)
          rw [f.2.keeps_iSupMem]
          apply Dcpo.iSupMem_le
          intro g h₂
          simp [f.2.keeps_iSup]
          apply Dcpo.iSup_le
          intro m
          rcases hs.2 _ h₁ _ h₂ with ⟨h, h₃, h₄, h₅⟩
          apply le_trans (h₄ _)
          apply le_trans (h.2.mono (iter_mono' h₅))
          apply le_trans' (Dcpo.le_iSupMem h₃)
          exact Dcpo.le_iSup (i := m + 1) (f := iter h)
      · apply Dcpo.iSupMem_le
        intro f h
        apply Dcpo.iSup_le
        intro n
        apply le_trans' (Dcpo.le_iSup (i := n))
        apply iter_mono'
        exact Dcpo.le_sSup h
  }

theorem fix_is_fixpoint : f (fix f) = fix f := by
  unfold fix
  rw [f.2.keeps_iSup]
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
    apply f.2.mono
    exact ih

end Domain
