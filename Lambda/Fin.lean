namespace List

variable {α : Type u}

inductive Fin : α → List α → Type u
| fz : List.Fin x (x :: l)
| fs : List.Fin x l → List.Fin x (y :: l)
infix:60 " ∈' " => Fin

def Fin.ofNatType (n : Nat) : Type u :=
  ∀ {x l}, ofNatTypeAux n x (x :: l)
where
  ofNatTypeAux : Nat → α → List α → Type u
  | 0, x, l => x ∈' l
  | m + 1, x, l => ∀ {y}, ofNatTypeAux m x (y :: l)

@[simp] def Fin.ofNat (n : Nat) : @Fin.ofNatType α n :=
  ofNatAux n fz
where
  @[simp] ofNatAux {x : α} {l : List α} :
    (n : Nat) → x ∈' l → ofNatType.ofNatTypeAux n x l
  | 0 => λ h => h
  | n + 1 => λ h {_} => (ofNatAux n (fs h))

def Fin.mem : x ∈' l → x ∈ l
| fz => Mem.head _
| fs h => Mem.tail _ (mem h)

def Fin.fin : x ∈' l → _root_.Fin l.length
| fz => ⟨0, Nat.zero_lt_succ _⟩
| fs h => match fin h with
          | ⟨n, h⟩ => ⟨n + 1, Nat.succ_le_succ h⟩

theorem Fin.fin_get (h : x ∈' l) : l.get (fin h) = x := by
  induction h with
  | fz => rfl
  | fs h ih => simp [get, ←ih]

end List



inductive Fin' : Nat → Type where
| fz : Fin' (n + 1)
| fs : Fin' n → Fin' (n + 1)

def Fin'.ofNat : (n : Nat) → Fin' (m + n + 1)
| 0 => fz
| n + 1 => fs (ofNat n)

def Fin'.ofNat_le : ∀ {m} (n), n < m → Fin' m
| _ + 1, 0, _ => fz
| _ + 1, (n + 1), h => fs (ofNat_le n (Nat.le_of_succ_le_succ h))

inductive Vec (α : Type u) : Nat → Type u where
| nil : Vec α 0
| cons : α → Vec α n → Vec α (n + 1)

notation "[]ᵥ" => Vec.nil
infixr:55 " ∷ᵥ " => Vec.cons

def Vec.get : Vec α n → Fin' n → α
| a ∷ᵥ _, Fin'.fz => a
| _ ∷ᵥ v, Fin'.fs x => v.get x
