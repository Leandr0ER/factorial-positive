import Mathlib.Data.Nat.Basic

def fac : ℕ →  ℕ 
  | 0 => 1
  | n+1 => (n+1) * fac n

theorem fac_pos (n: ℕ) : 0 < fac n := by
  induction n with
  | zero =>
    simp [fac]
  | succ n ih =>
    unfold fac
    exact Nat.mul_pos (Nat.succ_pos n) ih
