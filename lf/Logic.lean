import lf.Tactics

namespace LF
namespace Logic

-- =================================================================
-- Basic Propositions
-- =================================================================

theorem plus_2_2_is_4 : 2 + 2 = 4 := by rfl

def plus_claim : Prop := 2 + 2 = 4

theorem plus_claim_is_true : plus_claim := by rfl

def is_three (n : Nat) : Prop := n = 3

def injective {A B : Type} (f : A → B) : Prop := ∀ (x y : A), f x = f y → x = y

-- Coq Style
-- lemma succ_inj : injective Nat.succ := by
--   intro x y H
--   injection H
theorem succ_inj : injective Nat.succ := by
  intro x y H
  injection H

-- =================================================================
-- Conjunction
-- =================================================================

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  constructor
  · rfl
  · rfl

example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  exact ⟨rfl, rfl⟩

-- Exercise: plus_is_O (2 stars)
theorem plus_is_O {n m : Nat} (H : n + m = 0) : n = 0 ∧ m = 0 := by
  sorry

theorem and_example2 {n m : Nat} (H : n = 0 ∧ m = 0) : n + m = 0 := by
  cases H with | intro Hn Hm =>
  rw [Hn, Hm]

theorem and_example2' {n m : Nat} (H : n = 0 ∧ m = 0) : n + m = 0 := by
  have ⟨Hn, Hm⟩ := H
  rw [Hn, Hm]

theorem and_example2'' {n m : Nat} (Hn : n = 0) (Hm : m = 0) : n + m = 0 := by
  rw [Hn, Hm]

theorem and_example3 {n m : Nat} (H : n + m = 0) : n * m = 0 := by
  have ⟨Hn, Hm⟩ := plus_is_O H
  rw [Hn]
  simp

theorem proj1 {P Q : Prop} (H : P ∧ Q) : P := by
  have ⟨HP, _⟩ := H
  exact HP

-- Exercise: proj2 (1 star)
theorem proj2 {P Q : Prop} (H : P ∧ Q) : Q := by
  sorry

theorem and_commut {P Q : Prop} (H : P ∧ Q) : Q ∧ P := by
  have ⟨HP, HQ⟩ := H
  exact ⟨HQ, HP⟩

-- Exercise: and_assoc (1 star)
theorem and_assoc {P Q R : Prop} (H : P ∧ (Q ∧ R)) : (P ∧ Q) ∧ R := by
  sorry

-- =================================================================
-- Disjunction
-- =================================================================

theorem factor_is_O {n m : Nat} (H : n = 0 ∨ m = 0) : n * m = 0 := by
  cases H with
  | inl Hn =>
    rw [Hn]
    simp
  | inr Hm =>
    rw [Hm]
    omega

theorem or_intro_l {A B : Prop} (HA : A) : A ∨ B := by
  exact Or.inl HA

theorem zero_or_succ (n : Nat) : n = 0 ∨ n = (n - 1) + 1 := by
  cases n with
  | zero => exact Or.inl rfl
  | succ n' => exact Or.inr (by omega)

-- Exercise: mult_is_O (2 stars)
theorem mult_is_O {n m : Nat} (H : n * m = 0) : n = 0 ∨ m = 0 := by
  sorry

-- Exercise: or_commut (1 star)
theorem or_commut {P Q : Prop} (H : P ∨ Q) : Q ∨ P := by
  sorry

-- =================================================================
-- Falsehood and Negation
-- =================================================================

theorem ex_falso_quodlibet {P : Prop} (contra : False) : P := by
  cases contra

-- Exercise: not_implies_our_not (2 stars)
theorem not_implies_our_not {P : Prop} (H : ¬ P) : ∀ (Q : Prop), P → Q := by
  sorry

theorem zero_not_one : 0 ≠ 1 := by
  intro contra
  injection contra

theorem not_False : ¬ False := by
  intro H
  cases H

theorem contradiction_implies_anything {P Q : Prop} (H : P ∧ ¬ P) : Q := by
  have ⟨HP, HNP⟩ := H
  exact False.elim (HNP HP)

theorem double_neg {P : Prop} (H : P) : ¬ ¬ P := by
  intro G
  exact G H

-- Exercise: contrapositive (1 star)
theorem contrapositive {P Q : Prop} (H : P → Q) : ¬ Q → ¬ P := by
  sorry

-- Exercise: not_both_true_and_false (1 star)
theorem not_both_true_and_false {P : Prop} : ¬ (P ∧ ¬ P) := by
  sorry

-- Exercise: de_morgan_not_or (2 stars)
theorem de_morgan_not_or {P Q : Prop} (H : ¬ (P ∨ Q)) : ¬ P ∧ ¬ Q := by
  sorry

-- Exercise: not_S_inverse_pred (1 star)
theorem not_S_pred_n : ¬ (∀ n : Nat, Nat.succ (n - 1) = n) := by
  sorry

theorem not_true_is_false {b : Bool} (H : b ≠ true) : b = false := by
  cases b
  · rfl
  · contradiction

theorem not_true_is_false' {b : Bool} (H : b ≠ true) : b = false := by
  cases b
  · rfl
  · contradiction

-- =================================================================
-- Truth
-- =================================================================

theorem True_is_true : True := by
  exact trivial

def disc_fn (n : Nat) : Prop :=
  match n with
  | 0 => True
  | _ + 1 => False

theorem disc_example {n : Nat} : ¬ (0 = n + 1) := by
  intro contra
  have H : disc_fn 0 := trivial
  rw [contra] at H
  exact H

-- Exercise: nil_is_not_cons (2 stars)
theorem nil_is_not_cons {X : Type} (x : X) (xs : Poly.List X) : ¬ (Poly.List.nil = Poly.List.cons x xs) := by
  sorry

-- =================================================================
-- Logical Equivalence
-- =================================================================

theorem iff_sym {P Q : Prop} (H : P ↔ Q) : Q ↔ P := by
  have ⟨HPQ, HQP⟩ := H
  exact ⟨HQP, HPQ⟩

theorem not_true_iff_false {b : Bool} : b ≠ true ↔ b = false := by
  constructor
  · apply not_true_is_false
  · intro H
    rw [H]
    intro H2
    contradiction

theorem apply_iff_example1 {P Q R : Prop} (Hiff : P ↔ Q) (HP : Q → R) (H : P) : R := by
  apply HP
  apply Hiff.mp H

theorem apply_iff_example2 {P Q R : Prop} (Hiff : P ↔ Q) (HQ : P → R) (H : Q) : R := by
  apply HQ
  apply Hiff.mpr H

-- Exercise: iff_refl (1 star)
theorem iff_refl {P : Prop} : P ↔ P := by
  sorry

-- Exercise: iff_trans (1 star)
theorem iff_trans {P Q R : Prop} (H1 : P ↔ Q) (H2 : Q ↔ R) : P ↔ R := by
  sorry

-- Exercise: or_distributes_over_and (3 stars)
theorem or_distributes_over_and {P Q R : Prop} : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  sorry

-- =================================================================
-- Setoids and Logical Equivalence
-- =================================================================

theorem mul_eq_0 {n m : Nat} : n * m = 0 ↔ n = 0 ∨ m = 0 := by
  constructor
  · apply mult_is_O
  · apply factor_is_O

theorem or_assoc {P Q R : Prop} : P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R := by
  constructor
  · intro H
    cases H with
    | inl HP => exact Or.inl (Or.inl HP)
    | inr HQR =>
      cases HQR with
      | inl HQ => exact Or.inl (Or.inr HQ)
      | inr HR => exact Or.inr HR
  · intro H
    cases H with
    | inl HPQ =>
      cases HPQ with
      | inl HP => exact Or.inl HP
      | inr HQ => exact Or.inr (Or.inl HQ)
    | inr HR => exact Or.inr (Or.inr HR)

theorem mul_eq_0_ternary {n m p : Nat} : n * m * p = 0 ↔ n = 0 ∨ m = 0 ∨ p = 0 := by
  rw [mul_eq_0, mul_eq_0, or_assoc]

-- =================================================================
-- Existential Quantification
-- =================================================================

def Even (x : Nat) := ∃ n : Nat, x = 2 * n

theorem four_is_Even : Even 4 := by
  unfold Even
  exists 2

theorem exists_example_2 {n : Nat} (H : ∃ m, n = 4 + m) : ∃ o, n = 2 + o := by
  have ⟨m, Hm⟩ := H
  exists (2 + m)
  rw [Hm]
  omega

-- Exercise: dist_not_exists (1 star)
theorem dist_not_exists {X : Type} {P : X → Prop} (H : ∀ x, P x) : ¬ (∃ x, ¬ P x) := by
  sorry

-- Exercise: dist_exists_or (2 stars)
theorem dist_exists_or {X : Type} {P Q : X → Prop} : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  sorry

-- Exercise: leb_plus_exists (3 stars)
theorem leb_plus_exists {n m : Nat} (H : (n ≤ m) = true) : ∃ x, m = n + x := by
  sorry

theorem plus_exists_leb {n m : Nat} (H : ∃ x, m = n + x) : (n ≤ m) = true := by
  sorry

-- =================================================================
-- Programming with Propositions
-- =================================================================

def In {A : Type} (x : A) (l : Poly.List A) : Prop :=
  match l with
  | .nil => False
  | .cons x' l' => x' = x ∨ In x l'

-- Exercise: In_map_iff (2 stars)
theorem In_map_iff {A B : Type} (f : A → B) (l : Poly.List A) (y : B) :
  In y (Poly.map f l) ↔ ∃ x, f x = y ∧ In x l := by sorry

-- Exercise: In_app_iff (2 stars)
theorem In_app_iff {A : Type} {l l' : Poly.List A} {a : A} :
  In a (Poly.app l l') ↔ In a l ∨ In a l' := by sorry

-- Exercise: All (3 stars)
def All {T : Type} (P : T → Prop) (l : Poly.List T) : Prop := sorry

theorem All_In {T : Type} {P : T → Prop} {l : Poly.List T} :
  (∀ x, In x l → P x) ↔ All P l := by sorry

-- Exercise: combine_odd_even (2 stars)
def combine_odd_even (Podd Peven : Nat → Prop) (n : Nat) : Prop := sorry

theorem combine_odd_even_intro {Podd Peven : Nat → Prop} {n : Nat}
  (Hodd : LF.odd n = true → Podd n)
  (Heven : LF.odd n = false → Peven n) :
  combine_odd_even Podd Peven n := by sorry

theorem combine_odd_even_elim_odd {Podd Peven : Nat → Prop} {n : Nat}
  (H : combine_odd_even Podd Peven n) (Hodd : LF.odd n = true) : Podd n := by sorry

theorem combine_odd_even_elim_even {Podd Peven : Nat → Prop} {n : Nat}
  (H : combine_odd_even Podd Peven n) (Heven : LF.odd n = false) : Peven n := by sorry

-- =================================================================
-- Working with Decidable Properties
-- =================================================================

-- Exercise: even_double_conv (3 stars)
theorem even_double_conv {n : Nat} : ∃ k, n = if LF.even n = true then Tactics.double k else (Tactics.double k) + 1 := by sorry

-- =================================================================
-- The Logic of Rocq
-- =================================================================

-- Exercise: logical_connectives (2 stars)
theorem andb_true_iff {b1 b2 : Bool} : (b1 && b2) = true ↔ b1 = true ∧ b2 = true := by sorry

theorem orb_true_iff {b1 b2 : Bool} : (b1 || b2) = true ↔ b1 = true ∨ b2 = true := by sorry

-- Exercise: eqb_neq (1 star)
theorem eqb_neq {x y : Nat} : (x == y) = false ↔ x ≠ y := by sorry

-- Exercise: eqb_list (3 stars)
def eqb_list {A : Type} (eqb : A → A → Bool) (l1 l2 : Poly.List A) : Bool := sorry

theorem eqb_list_true_iff {A : Type} (eqb : A → A → Bool)
  (eqb_true_iff : ∀ a1 a2, eqb a1 a2 = true ↔ a1 = a2)
  (l1 l2 : Poly.List A) : eqb_list eqb l1 l2 = true ↔ l1 = l2 := by sorry

-- Exercise: All_forallb (2 stars)
theorem forallb_true_iff {X : Type} (test : X → Bool) (l : Poly.List X) :
  Tactics.forallb test l = true ↔ All (fun x => test x = true) l := by sorry

-- =================================================================
-- Functional Extensionality
-- =================================================================

axiom functional_extensionality {X Y : Type} {f g : X → Y} (H : ∀ x, f x = g x) : f = g

def rev_append {X : Type} (l1 l2 : Poly.List X) : Poly.List X :=
  match l1 with
  | .nil => l2
  | .cons x l1' => rev_append l1' (.cons x l2)

def tr_rev {X : Type} (l : Poly.List X) : Poly.List X :=
  rev_append l .nil

-- Exercise: tr_rev_correct (4 stars)
theorem tr_rev_correct {X : Type} (l : Poly.List X) : tr_rev l = Poly.rev l := by sorry

-- =================================================================
-- Classical vs. Constructive Logic
-- =================================================================

def excluded_middle := ∀ P : Prop, P ∨ ¬ P

-- Exercise: excluded_middle_irrefutable (3 stars)
theorem excluded_middle_irrefutable : ∀ P : Prop, ¬ ¬ (P ∨ ¬ P) := by sorry

-- Exercise: not_exists_dist (3 stars)
theorem not_exists_dist {X : Type} (P : X → Prop) :
  excluded_middle → ¬ (∃ x, ¬ P x) → (∀ x, P x) := by sorry

-- Exercise: classical_axioms (5 stars)
def peirce := ∀ P Q : Prop, ((P → Q) → P) → P
def double_negation_elimination := ∀ P : Prop, ¬ ¬ P → P
def de_morgan_not_and_not := ∀ P Q : Prop, ¬ (¬ P ∧ ¬ Q) → P ∨ Q
def implies_to_or := ∀ P Q : Prop, (P → Q) → (¬ P ∨ Q)
def consequentia_mirabilis := ∀ P : Prop, (¬ P → P) → P

theorem classical_axioms_equiv :
  (peirce ↔ double_negation_elimination) ∧
  (double_negation_elimination ↔ de_morgan_not_and_not) ∧
  (de_morgan_not_and_not ↔ implies_to_or) ∧
  (implies_to_or ↔ consequentia_mirabilis) ∧
  (consequentia_mirabilis ↔ excluded_middle) := by sorry

end Logic
end LF
