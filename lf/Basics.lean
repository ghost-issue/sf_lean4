namespace LF

-- =================================================================
-- Enumerated Types and Days of the Week
-- =================================================================

inductive Day : Type where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday

def nextWorkingDay (d : Day) : Day :=
  match d with
  | .monday    => .tuesday
  | .tuesday   => .wednesday
  | .wednesday => .thursday
  | .thursday  => .friday
  | .friday    => .monday
  | .saturday  => .monday
  | .sunday    => .monday

#eval nextWorkingDay .friday
#eval nextWorkingDay (nextWorkingDay .saturday)

example : nextWorkingDay (nextWorkingDay .saturday) = .tuesday := rfl

-- =================================================================
-- Booleans
-- =================================================================

namespace BoolPlayground

inductive Bool : Type where
  | true
  | false
  deriving DecidableEq

def negb (b : Bool) : Bool :=
  match b with
  | .true  => .false
  | .false => .true

def andb (b1 b2 : Bool) : Bool :=
  match b1 with
  | .true  => b2
  | .false => .false

def orb (b1 b2 : Bool) : Bool :=
  match b1 with
  | .true  => .true
  | .false => b2

example : orb .true .false = .true := rfl
example : orb .false .false = .false := rfl
example : orb .false .true = .true := rfl
example : orb .true .true = .true := rfl

infixl:40 " && " => andb
infixl:50 " || " => orb

example : orb .false (orb .false .true) = .true := rfl

def negb' (b : Bool) : Bool :=
  if b = .true then .false else .true

def andb' (b1 b2 : Bool) : Bool :=
  if b1 = .true then b2 else .false

def orb' (b1 b2 : Bool) : Bool :=
  if b1 = .true then .true else b2

end BoolPlayground

-- We switch to standard Lean Bool for the exercises to leverage native if-then-else
-- and standard notations if desired, or we can just use Lean's Bool.

inductive Bw : Type where
  | black
  | white

def invert (x : Bw) : Bw :=
  match x with
  | .black => .white
  | .white => .black

#eval invert .black
#eval invert .white

-- Exercise: nandb (1 star)
def nandb (b1 b2 : Bool) : Bool :=
  sorry

example : nandb true false = true := sorry
example : nandb false false = true := sorry
example : nandb false true = true := sorry
example : nandb true true = false := sorry

-- Exercise: andb3 (1 star)
def andb3 (b1 b2 b3 : Bool) : Bool :=
  sorry

example : andb3 true true true = true := sorry
example : andb3 false true true = false := sorry
example : andb3 true false true = false := sorry
example : andb3 true true false = false := sorry

-- =================================================================
-- Types and New Types from Old
-- =================================================================

#check true
#check not true
#check not

inductive Rgb : Type where
  | red
  | green
  | blue

inductive Color : Type where
  | black
  | white
  | primary (p : Rgb)

def monochrome (c : Color) : Bool :=
  match c with
  | .black => true
  | .white => true
  | .primary _ => false

def isred (c : Color) : Bool :=
  match c with
  | .black => false
  | .white => false
  | .primary .red => true
  | .primary _ => false

-- =================================================================
-- Modules
-- =================================================================

namespace Playground
  def foo : Rgb := .blue
end Playground

def foo : Bool := true

#check Playground.foo
#check foo

-- =================================================================
-- Tuples
-- =================================================================

namespace TuplePlayground

inductive Bit : Type where
  | B1
  | B0

inductive Nybble : Type where
  | bits (b0 b1 b2 b3 : Bit)

#check Nybble.bits .B1 .B0 .B1 .B0

def allZero (nb : Nybble) : Bool :=
  match nb with
  | .bits .B0 .B0 .B0 .B0 => true
  | _ => false

-- To enable #eval for these custom types we could use deriving Repr or just check:
-- #eval allZero (.bits .B1 .B0 .B1 .B0)
-- #eval allZero (.bits .B0 .B0 .B0 .B0)

end TuplePlayground

-- =================================================================
-- Numbers
-- =================================================================

namespace NatPlayground

inductive Nat : Type where
  | O
  | S (n : Nat)

def pred (n : Nat) : Nat :=
  match n with
  | .O => .O
  | .S n' => n'

end NatPlayground

-- Returning to standard Nat
def minustwo (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | n' + 2 => n'

#eval minustwo 4

#check Nat.succ
#check Nat.pred
#check minustwo

def even (n : Nat) : Bool :=
  match n with
  | 0 => true
  | 1 => false
  | n' + 2 => even n'

def odd (n : Nat) : Bool :=
  not (even n)

example : odd 1 = true := rfl
example : odd 4 = false := rfl

namespace NatPlayground2

def plus (n m : Nat) : Nat :=
  match n with
  | 0 => m
  | n' + 1 => (plus n' m) + 1

#eval plus 3 2

def mult (n m : Nat) : Nat :=
  match n with
  | 0 => 0
  | n' + 1 => plus m (mult n' m)

example : mult 3 3 = 9 := rfl

def minus (n m : Nat) : Nat :=
  match n, m with
  | 0, _ => 0
  | n, 0 => n
  | n' + 1, m' + 1 => minus n' m'

end NatPlayground2

def exp (base power : Nat) : Nat :=
  match power with
  | 0 => 1
  | p + 1 => base * (exp base p)

-- Exercise: factorial (1 star)
def factorial (n : Nat) : Nat :=
  sorry

example : factorial 3 = 6 := sorry
example : factorial 5 = 10 * 12 := sorry

-- Booleans logic with equality
def eqb (n m : Nat) : Bool :=
  match n, m with
  | 0, 0 => true
  | 0, _ + 1 => false
  | _ + 1, 0 => false
  | n' + 1, m' + 1 => eqb n' m'

def leb (n m : Nat) : Bool :=
  match n, m with
  | 0, _ => true
  | _ + 1, 0 => false
  | n' + 1, m' + 1 => leb n' m'

example : leb 2 2 = true := rfl
example : leb 2 4 = true := rfl
example : leb 4 2 = false := rfl

-- We can use Nat.ble built into Lean as well, but using leb directly here.
infix:70 " =? " => eqb
infix:70 " <=? " => leb

example : (4 <=? 2) = false := rfl

-- Exercise: ltb (1 star)
def ltb (n m : Nat) : Bool :=
  sorry

infix:70 " <? " => ltb

example : (2 <? 2) = false := sorry
example : (2 <? 4) = true := sorry
example : (4 <? 2) = false := sorry

-- =================================================================
-- Proof by Simplification
-- =================================================================

example : 1 + 1 = 2 := by
  rfl

theorem plus_O_n (n : Nat) : 0 + n = n := by
  simp

theorem plus_O_n' (n : Nat) : 0 + n = n := by
  simp

theorem plus_O_n'' (m : Nat) : 0 + m = m := by
  simp

theorem plus_1_l (n : Nat) : 1 + n = n + 1 := by
  rw [Nat.add_comm]

theorem mult_0_l (n : Nat) : 0 * n = 0 := by
  simp

-- =================================================================
-- Proof by Rewriting
-- =================================================================

theorem plus_id_example (n m : Nat) (H : n = m) : n + n = m + m := by
  rw [H]

-- Exercise: plus_id_exercise (1 star)
theorem plus_id_exercise (n m o : Nat) (H1 : n = m) (H2 : m = o) : n + m = m + o := by
  sorry

#check Nat.mul_zero
#check Nat.mul_succ

-- Keeping aliases for Coq theorems used in the text
theorem mult_n_O (n : Nat) : 0 = n * 0 := by
  rw [Nat.mul_zero]

theorem mult_n_Sm (n m : Nat) : n * m + n = n * (m + 1) := by
  rw [Nat.mul_succ, Nat.add_comm]

theorem mult_n_0_m_0 (p q : Nat) : (p * 0) + (q * 0) = 0 := by
  rw [← mult_n_O p]
  rw [← mult_n_O q]

-- Exercise: mult_n_1 (1 star)
theorem mult_n_1 (p : Nat) : p * 1 = p := by
  sorry

-- =================================================================
-- Proof by Case Analysis
-- =================================================================

def negb (b : Bool) : Bool := !b
def andb (b1 b2 : Bool) : Bool := b1 && b2
def orb (b1 b2 : Bool) : Bool := b1 || b2

theorem plus_1_neq_0 (n : Nat) : (n + 1) =? 0 = false := by
  cases n with
  | zero => rfl
  | succ n' => rfl

theorem negb_involutive (b : Bool) : negb (negb b) = b := by
  cases b with
  | true => rfl
  | false => rfl

theorem andb_commutative (b c : Bool) : andb b c = andb c b := by
  cases b <;> cases c <;> rfl

theorem andb_commutative' (b c : Bool) : andb b c = andb c b :=
  andb_commutative b c

theorem andb3_exchange (b c d : Bool) : andb (andb b c) d = andb (andb b d) c := by
  cases b <;> cases c <;> cases d <;> rfl

-- Exercise: andb_true_elim2 (2 stars)
theorem andb_true_elim2 (b c : Bool) (H : andb b c = true) : c = true := by
  sorry

theorem plus_1_neq_0' (n : Nat) : (n + 1) =? 0 = false :=
  plus_1_neq_0 n

theorem andb_commutative'' (b c : Bool) : andb b c = andb c b :=
  andb_commutative b c

-- Exercise: zero_nbeq_plus_1 (1 star)
theorem zero_nbeq_plus_1 (n : Nat) : 0 =? (n + 1) = false := by
  sorry

-- =================================================================
-- More Exercises
-- =================================================================

-- Exercise: identity_fn_applied_twice (1 star)
theorem identity_fn_applied_twice (f : Bool → Bool)
  (H : ∀ x : Bool, f x = x) (b : Bool) : f (f b) = b := by
  sorry

-- Exercise: negation_fn_applied_twice (1 star)
theorem negation_fn_applied_twice (f : Bool → Bool)
  (H : ∀ x : Bool, f x = negb x) (b : Bool) : f (f b) = b := by
  sorry

-- Exercise: andb_eq_orb (3 stars)
theorem andb_eq_orb (b c : Bool) (H : andb b c = orb b c) : b = c := by
  sorry

namespace LateDays

inductive Letter : Type where
  | A | B | C | D | F

inductive Modifier : Type where
  | Plus | Natural | Minus

inductive Grade : Type where
  | Grade (l : Letter) (m : Modifier)

inductive Comparison : Type where
  | Eq | Lt | Gt

def letter_comparison (l1 l2 : Letter) : Comparison :=
  match l1, l2 with
  | .A, .A => .Eq
  | .A, _ => .Gt
  | .B, .A => .Lt
  | .B, .B => .Eq
  | .B, _ => .Gt
  | .C, .A | .C, .B => .Lt
  | .C, .C => .Eq
  | .C, _ => .Gt
  | .D, .A | .D, .B | .D, .C => .Lt
  | .D, .D => .Eq
  | .D, _ => .Gt
  | .F, .A | .F, .B | .F, .C | .F, .D => .Lt
  | .F, .F => .Eq

-- Exercise: letter_comparison_Eq (1 star)
theorem letter_comparison_Eq (l : Letter) : letter_comparison l l = .Eq := by
  sorry

def modifier_comparison (m1 m2 : Modifier) : Comparison :=
  match m1, m2 with
  | .Plus, .Plus => .Eq
  | .Plus, _ => .Gt
  | .Natural, .Plus => .Lt
  | .Natural, .Natural => .Eq
  | .Natural, _ => .Gt
  | .Minus, .Plus | .Minus, .Natural => .Lt
  | .Minus, .Minus => .Eq

-- Exercise: grade_comparison (2 stars)
def grade_comparison (g1 g2 : Grade) : Comparison :=
  sorry

example : grade_comparison (.Grade .A .Minus) (.Grade .B .Plus) = .Gt := sorry
example : grade_comparison (.Grade .A .Minus) (.Grade .A .Plus) = .Lt := sorry
example : grade_comparison (.Grade .F .Plus) (.Grade .F .Plus) = .Eq := sorry
example : grade_comparison (.Grade .B .Minus) (.Grade .C .Plus) = .Gt := sorry

def lower_letter (l : Letter) : Letter :=
  match l with
  | .A => .B
  | .B => .C
  | .C => .D
  | .D => .F
  | .F => .F

theorem lower_letter_F_is_F : lower_letter .F = .F := rfl

-- Exercise: lower_letter_lowers (2 stars)
theorem lower_letter_lowers (l : Letter)
  (H : letter_comparison .F l = .Lt) :
  letter_comparison (lower_letter l) l = .Lt := by
  sorry

-- Exercise: lower_grade (2 stars)
def lower_grade (g : Grade) : Grade :=
  sorry

example : lower_grade (.Grade .A .Plus) = .Grade .A .Natural := sorry
example : lower_grade (.Grade .A .Natural) = .Grade .A .Minus := sorry
example : lower_grade (.Grade .A .Minus) = .Grade .B .Plus := sorry
example : lower_grade (.Grade .B .Plus) = .Grade .B .Natural := sorry
example : lower_grade (.Grade .F .Natural) = .Grade .F .Minus := sorry
example : lower_grade (lower_grade (.Grade .B .Minus)) = .Grade .C .Natural := sorry
example : lower_grade (lower_grade (lower_grade (.Grade .B .Minus))) = .Grade .C .Minus := sorry

theorem lower_grade_F_Minus : lower_grade (.Grade .F .Minus) = .Grade .F .Minus := by
  sorry

-- Exercise: lower_grade_lowers (3 stars)
theorem lower_grade_lowers (g : Grade)
  (H : grade_comparison (.Grade .F .Minus) g = .Lt) :
  grade_comparison (lower_grade g) g = .Lt := by
  sorry

def apply_late_policy (late_days : Nat) (g : Grade) : Grade :=
  if (late_days <? 9) = true then g
  else if (late_days <? 17) = true then lower_grade g
  else if (late_days <? 21) = true then lower_grade (lower_grade g)
  else lower_grade (lower_grade (lower_grade g))

theorem apply_late_policy_unfold (late_days : Nat) (g : Grade) :
  apply_late_policy late_days g =
    if (late_days <? 9) = true then g
    else if (late_days <? 17) = true then lower_grade g
    else if (late_days <? 21) = true then lower_grade (lower_grade g)
    else lower_grade (lower_grade (lower_grade g)) := by
  rfl

-- Exercise: no_penalty_for_mostly_on_time (2 stars)
theorem no_penalty_for_mostly_on_time (late_days : Nat) (g : Grade)
  (H : (late_days <? 9) = true) :
  apply_late_policy late_days g = g := by
  sorry

-- Exercise: grade_lowered_once (2 stars)
theorem grade_lowered_once (late_days : Nat) (g : Grade)
  (H1 : (late_days <? 9) = false)
  (H2 : (late_days <? 17) = true) :
  apply_late_policy late_days g = lower_grade g := by
  sorry

end LateDays

-- =================================================================
-- Binary Numerals
-- =================================================================

-- Exercise: binary (3 stars)
inductive Bin : Type where
  | Z
  | B0 (n : Bin)
  | B1 (n : Bin)

def incr (m : Bin) : Bin :=
  sorry

def bin_to_nat (m : Bin) : Nat :=
  sorry

example : incr (.B1 .Z) = .B0 (.B1 .Z) := sorry
example : incr (.B0 (.B1 .Z)) = .B1 (.B1 .Z) := sorry
example : incr (.B1 (.B1 .Z)) = .B0 (.B0 (.B1 .Z)) := sorry
example : bin_to_nat (.B0 (.B1 .Z)) = 2 := sorry
example : bin_to_nat (incr (.B1 .Z)) = 1 + bin_to_nat (.B1 .Z) := sorry
example : bin_to_nat (incr (incr (.B1 .Z))) = 2 + bin_to_nat (.B1 .Z) := sorry
example : bin_to_nat (.B0 (.B0 (.B0 (.B1 .Z)))) = 8 := sorry

end LF
