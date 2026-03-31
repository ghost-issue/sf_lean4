import lf.Poly

namespace LF
namespace Tactics

-- =================================================================
-- The apply Tactic
-- =================================================================

theorem silly1 {n m : Nat} (eq : n = m) : n = m := by
  apply eq

theorem silly2 {n m o p : Nat} (eq1 : n = m) (eq2 : n = m → [n, o] = [m, p]) : [n, o] = [m, p] := by
  apply eq2
  apply eq1

theorem silly2a {n m : Nat}
  (eq1 : (n, n) = (m, m))
  (eq2 : ∀ q r : Nat, (q, q) = (r, r) → [q] = [r]) : [n] = [m] := by
  apply eq2
  apply eq1

-- Exercise: silly_ex (2 stars)
-- Coq Style
-- theorem silly_ex {p : Nat}
--   (H1 : ∀ n, Nat.even n = true → Nat.even (n + 1) = false)
--   (H2 : ∀ n, Nat.even n = false → Nat.odd n = true)
--   (H3 : Nat.even p = true) :
--   Nat.odd (p + 1) = true := by
--   sorry
theorem silly_ex {p : Nat}
  (H1 : ∀ n, LF.even n = true → LF.even (n + 1) = false)
  (H2 : ∀ n, LF.even n = false → LF.odd n = true)
  (H3 : LF.even p = true) :
  LF.odd (p + 1) = true := by
  sorry

theorem silly3 {n m : Nat} (H : n = m) : m = n := by
  symm
  apply H

-- Exercise: apply_exercise1 (2 stars)
theorem rev_exercise1 {l l' : Poly.List Nat} (H : l = Poly.rev l') : l' = Poly.rev l := by
  sorry

-- =================================================================
-- The apply with Tactic
-- =================================================================

example {a b c d e f : Nat} (eq1 : [a, b] = [c, d]) (eq2 : [c, d] = [e, f]) : [a, b] = [e, f] := by
  rw [eq1]
  apply eq2

theorem trans_eq {X : Type} {x y z : X} (eq1 : x = y) (eq2 : y = z) : x = z := by
  rw [eq1]
  apply eq2

example {a b c d e f : Nat} (eq1 : [a, b] = [c, d]) (eq2 : [c, d] = [e, f]) : [a, b] = [e, f] := by
  apply trans_eq eq1 eq2

-- Exercise: trans_eq_exercise (3 stars)
example {n m o p : Nat} (H1 : m = o - 2) (H2 : n + p = m) : n + p = o - 2 := by
  sorry

-- =================================================================
-- The injection and discriminate Tactics
-- =================================================================

-- Coq Style *
-- theorem S_injective {n m : Nat} (H : n + 1 = m + 1) : n = m := by
--   injection H as Hnm
--   apply Hnm
theorem S_injective {n m : Nat} (H : n + 1 = m + 1) : n = m := by
  injection H

-- Coq Style *
-- theorem injection_ex1 {n m o : Nat} (H : [n, m] = [o, o]) : n = m := by
--   injection H with H1 H2
--   rw [H1]
--   rw [H2]
theorem injection_ex1 {n m o : Nat} (H : [n, m] = [o, o]) : n = m := by
  injection H with H1 H2
  injection H2 with H3 H4
  rw [H1, H3]

-- Exercise: injection_ex3 (3 stars)
example {X : Type} {x y z : X} {l j : List X} (H1 : x :: y :: l = z :: j) (H2 : j = z :: l) : x = y := by
  sorry

theorem discriminate_ex1 {n m : Nat} (contra : false = true) : n = m := by
  contradiction

theorem discriminate_ex2 {n : Nat} (contra : n + 1 = 0) : 2 + 2 = 5 := by
  contradiction

-- Exercise: discriminate_ex3 (1 star)
example {X : Type} {x y z : X} {l j : List X} (H : x :: y :: l = []) : x = z := by
  sorry

theorem eqb_0_l (n : Nat) : (0 == n) = true → n = 0 := by
  intro H
  cases n with
  | zero => rfl
  | succ n' => contradiction

theorem f_equal {A B : Type} (f : A → B) {x y : A} (eq : x = y) : f x = f y := by
  rw [eq]

-- Coq Style
-- theorem eq_implies_succ_equal {n m : Nat} (H : n = m) : n + 1 = m + 1 := by
--   apply f_equal
--   apply H
theorem eq_implies_succ_equal {n m : Nat} (H : n = m) : n + 1 = m + 1 := by
  apply congrArg (· + 1)
  apply H

-- =================================================================
-- Using Tactics on Hypotheses
-- =================================================================

-- Coq Style
-- theorem S_inj {n m : Nat} {b : Bool} (H : (n + 1 == m + 1) = b) : (n == m) = b := by
--   -- simpl in H is automatic via simp in Lean if needed
--   apply H
theorem S_inj {n m : Nat} {b : Bool} (H : (n + 1 == m + 1) = b) : (n == m) = b := by
  revert H
  simp

theorem silly4 {n m p q : Nat} (EQ : n = m → p = q) (H : m = n) : q = p := by
  symm at H
  have H2 := EQ H
  symm at H2
  apply H2

-- =================================================================
-- Specializing Hypotheses
-- =================================================================

theorem specialize_example {n : Nat} (H : ∀ m, m * n = 0) : n = 0 := by
  have H' := H 1
  -- rw mult_1_l in H' -- simplified in Lean
  sorry

-- Exercise: nth_error_always_none (3 stars)
-- Coq Style
-- lemma nth_error_always_none {l : Poly.List Nat} (H : ∀ i, Poly.nth_error l i = .none) : l = .nil := by
--   sorry
theorem nth_error_always_none {l : Poly.List Nat} (H : ∀ i, Poly.nth_error l i = .none) : l = .nil := by
  sorry

-- =================================================================
-- Varying the Induction Hypothesis
-- =================================================================

def double (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n' + 1 => double n' + 2

-- Coq Style
-- theorem double_injective {n m : Nat} (H : double n = double m) : n = m := by
--   revert m -- generalized dependent
--   induction n with
--   | zero =>
--     intro m eq
--     cases m with
--     | zero => rfl
--     | succ m' => contradiction
--   | succ n' IHn' =>
--     intro m eq
--     cases m with
--     | zero => contradiction
--     | succ m' =>
--       apply f_equal
--       -- injection eq ...
--       sorry
theorem double_injective {n m : Nat} (H : double n = double m) : n = m := by
  revert m
  induction n with
  | zero =>
    intro m eq
    cases m with
    | zero => rfl
    | succ m' => contradiction
  | succ n' IHn' =>
    intro m eq
    cases m with
    | zero => contradiction
    | succ m' =>
      apply congrArg (· + 1)
      sorry

-- Exercise: eqb_true (2 stars)
theorem eqb_true {n m : Nat} (H : (n == m) = true) : n = m := by sorry

-- Exercise: plus_n_n_injective (3 stars)
theorem plus_n_n_injective {n m : Nat} (H : n + n = m + m) : n = m := by sorry

-- =================================================================
-- Rewriting with conditional statements
-- =================================================================

-- Coq Style
-- lemma sub_add_leb {n m : Nat} (H : (n ≤ m) = true) : (m - n) + n = m := by
--   sorry
theorem sub_add_leb {n m : Nat} (H : (n ≤ m) = true) : (m - n) + n = m := by
  sorry

-- Exercise: nth_error_after_last (3 stars)
theorem nth_error_after_last {n : Nat} {X : Type} {l : Poly.List X} (H : Poly.length l = n) : Poly.nth_error l n = .none := by
  sorry

-- =================================================================
-- Unfolding Definitions
-- =================================================================

def square (n : Nat) := n * n

-- Coq Style
-- lemma square_mult {n m : Nat} : square (n * m) = square n * square m := by
--   unfold square
--   sorry
theorem square_mult {n m : Nat} : square (n * m) = square n * square m := by
  unfold square
  sorry

def foo (x : Nat) := 5

theorem silly_fact_1 {m : Nat} : foo m + 1 = foo (m + 1) + 1 := by
  rfl

def bar (x : Nat) :=
  match x with
  | 0 => 5
  | _ + 1 => 5

theorem silly_fact_2 {m : Nat} : bar m + 1 = bar (m + 1) + 1 := by
  cases m with
  | zero => rfl
  | succ m' => rfl

-- =================================================================
-- Using destruct on Compound Expressions
-- =================================================================

def sillyfun (n : Nat) : Bool :=
  if n == 3 then false
  else if n == 5 then false
  else false

theorem sillyfun_false {n : Nat} : sillyfun n = false := by
  unfold sillyfun
  split
  · rfl
  · split
    · rfl
    · rfl

-- Exercise: combine_split (3 stars)
theorem combine_split {X Y : Type} {l : Poly.List (Poly.Prod X Y)} {l1 : Poly.List X} {l2 : Poly.List Y}
  (H : Poly.split l = Poly.Prod.pair l1 l2) : Poly.combine l1 l2 = l := by
  sorry

def sillyfun1 (n : Nat) : Bool :=
  if n == 3 then true
  else if n == 5 then true
  else false

theorem sillyfun1_odd {n : Nat} (H : sillyfun1 n = true) : LF.odd n = true := by
  unfold sillyfun1 at H
  -- split logic
  sorry

-- Exercise: bool_fn_applied_thrice (2 stars)
theorem bool_fn_applied_thrice (f : Bool → Bool) (b : Bool) : f (f (f b)) = f b := by
  sorry

-- =================================================================
-- Additional Exercises
-- =================================================================

-- Exercise: eqb_sym (3 stars)
theorem eqb_sym {n m : Nat} : (n == m) = (m == n) := by sorry

-- Exercise: eqb_trans (3 stars)
theorem eqb_trans {n m p : Nat} (H1 : (n == m) = true) (H2 : (m == p) = true) : (n == p) = true := by sorry

-- Exercise: split_combine (3 stars)
def split_combine_statement : Prop := sorry
theorem split_combine_thm : split_combine_statement := sorry

-- Exercise: filter_exercise (3 stars)
theorem filter_exercise {X : Type} {test : X → Bool} {x : X} {l lf : Poly.List X}
  (H : Poly.filter test l = Poly.List.cons x lf) : test x = true := by sorry

-- Exercise: forall_exists_challenge (4 stars)
def forallb {X : Type} (test : X → Bool) (l : Poly.List X) : Bool := sorry
example : forallb LF.odd (.cons 1 (.cons 3 (.cons 5 (.nil)))) = true := by sorry

def existsb {X : Type} (test : X → Bool) (l : Poly.List X) : Bool := sorry
example : existsb (fun n => n == 5) (.cons 0 (.cons 2 (.cons 3 (.cons 6 .nil)))) = false := by sorry

def existsb' {X : Type} (test : X → Bool) (l : Poly.List X) : Bool := sorry

theorem existsb_existsb' {X : Type} {test : X → Bool} {l : Poly.List X} : existsb test l = existsb' test l := by sorry

end Tactics
end LF
