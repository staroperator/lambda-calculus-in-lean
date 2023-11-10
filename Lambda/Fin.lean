inductive Fin' : Nat → Type where
| fz : Fin' (n + 1)
| fs : Fin' n → Fin' (n + 1)

def Fin'.ofNat : ∀ {m} (n), n < m → Fin' m
| _ + 1, 0, _ => fz
| _ + 1, (n + 1), h => fs (Fin'.ofNat n (Nat.le_of_succ_le_succ h))
