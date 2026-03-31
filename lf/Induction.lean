import lf.Basics

namespace LF

-- =================================================================
-- Proof by Induction
-- =================================================================

theorem add_0_r_firsttry (n : Nat) : n + 0 = n := by
  -- simpl does nothing because + is defined by recursion on the second argument in Lean 4
  -- actually in Lean 4 `n + 0` is `n` definitionally, so rfl works immediately.
  -- but we follow the structure of the book.
  rfl

theorem add_0_r_secondtry (n : Nat) : n + 0 = n := by
  cases n with
  | zero => rfl
  | succ n' => rfl

theorem add_0_r (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n' ih => rfl

theorem minus_n_n (n : Nat) : n - n = 0 := by
  induction n with
  | zero => rfl
  | succ n' ih => omega

-- Exercise: mul_0_r (2 stars)
theorem mul_0_r (n : Nat) : n * 0 = 0 := by
  sorry

-- Exercise: plus_n_Sm (2 stars)
theorem plus_n_Sm (n m : Nat) : (n + m) + 1 = n + (m + 1) := by
  sorry

-- Exercise: add_comm (2 stars)
theorem add_comm (n m : Nat) : n + m = m + n := by
  sorry

-- Exercise: add_assoc (2 stars)
theorem add_assoc (n m p : Nat) : n + (m + p) = (n + m) + p := by
  sorry

-- Exercise: double_plus (2 stars)
def double (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n' + 1 => (double n') + 2

theorem double_plus (n : Nat) : double n = n + n := by
  sorry

-- Exercise: eqb_refl (2 stars)
theorem eqb_refl (n : Nat) : (n =? n) = true := by
  sorry

-- Exercise: even_S (2 stars)
theorem even_S (n : Nat) : even (n + 1) = not (even n) := by
  sorry

-- =================================================================
-- Proofs Within Proofs
-- =================================================================

theorem mult_0_plus' (n m : Nat) : (n + 0 + 0) * m = n * m := by
  have h : n + 0 + 0 = n := by
    simp
  rw [h]

theorem plus_rearrange (n m p q : Nat) : (n + m) + (p + q) = (m + n) + (p + q) := by
  have h : n + m = m + n := by
    rw [add_comm]
  rw [h]

-- =================================================================
-- More Exercises
-- =================================================================

-- Exercise: add_shuffle3 (3 stars)
theorem add_shuffle3 (n m p : Nat) : n + (m + p) = m + (n + p) := by
  sorry

-- Exercise: mul_comm (3 stars)
theorem mul_comm (m n : Nat) : m * n = n * m := by
  sorry

-- Exercise: leb_refl (3 stars, optional)
theorem leb_refl (n : Nat) : (n <=? n) = true := by
  sorry

-- Exercise: zero_neqb_S (3 stars, optional)
theorem zero_neqb_S (n : Nat) : (0 =? (n + 1)) = false := by
  sorry

-- Exercise: andb_false_r (3 stars, optional)
theorem andb_false_r (b : Bool) : andb b false = false := by
  sorry

-- Exercise: S_neqb_0 (3 stars, optional)
theorem S_neqb_0 (n : Nat) : ((n + 1) =? 0) = false := by
  sorry

-- Exercise: mult_1_l (3 stars, optional)
theorem mult_1_l (n : Nat) : 1 * n = n := by
  sorry

-- Exercise: all3_spec (3 stars, optional)
theorem all3_spec (b c : Bool) : orb (andb b c) (orb (negb b) (negb c)) = true := by
  sorry

-- Exercise: mult_plus_distr_r (3 stars, optional)
theorem mult_plus_distr_r (n m p : Nat) : (n + m) * p = (n * p) + (m * p) := by
  sorry

-- Exercise: mult_assoc (3 stars, optional)
theorem mult_assoc (n m p : Nat) : n * (m * p) = (n * m) * p := by
  sorry

-- =================================================================
-- Nat to Bin and Back to Nat
-- =================================================================

-- Exercise: binary_commute (3 stars)
theorem bin_to_nat_pres_incr (b : Bin) : bin_to_nat (incr b) = 1 + bin_to_nat b := by
  sorry

-- Exercise: nat_bin_nat (3 stars)
def nat_to_bin (n : Nat) : Bin :=
  sorry

theorem nat_bin_nat (n : Nat) : bin_to_nat (nat_to_bin n) = n := by
  sorry

-- =================================================================
-- Bin to Nat and Back to Bin (Advanced)
-- =================================================================

-- Exercise: double_bin (2 stars)
theorem double_incr (n : Nat) : double (n + 1) = (double n) + 2 := by
  sorry

def double_bin (b : Bin) : Bin :=
  sorry

theorem double_bin_zero : double_bin .Z = .Z := by
  sorry

theorem double_incr_bin (b : Bin) : double_bin (incr b) = incr (incr (double_bin b)) := by
  sorry

-- bin_nat_bin_fails text:
-- theorem bin_nat_bin_fails (b : Bin) : nat_to_bin (bin_to_nat b) = b
-- Abort.

-- Exercise: bin_nat_bin (4 stars)
def normalize (b : Bin) : Bin :=
  sorry

theorem bin_nat_bin (b : Bin) : nat_to_bin (bin_to_nat b) = normalize b := by
  sorry

end LF
