inductive Fin' : Nat → Type where
| fz : Fin' (n + 1)
| fs : Fin' n → Fin' (n + 1)

def Fin'.ofNat : ∀ {m} (n), n < m → Fin' m
| _ + 1, 0, _ => fz
| _ + 1, (n + 1), h => fs (Fin'.ofNat n (Nat.le_of_succ_le_succ h))

inductive Vec (α : Type u) : Nat → Type u where
| nil : Vec α 0
| cons : α → Vec α n → Vec α (n + 1)

notation "[]ᵥ" => Vec.nil
infixr:55 " ∷ᵥ " => Vec.cons

instance : EmptyCollection (Vec α 0) := ⟨[]ᵥ⟩
@[simp] def Vec.add (v : Vec α n) (x : α) := x ∷ᵥ v
infixl:55 ",' " => Vec.add

def Vec.get : Vec α n → Fin' n → α
| a ∷ᵥ _, Fin'.fz => a
| _ ∷ᵥ v, Fin'.fs x => v.get x
