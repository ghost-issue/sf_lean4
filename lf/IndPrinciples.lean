import lf.ProofObjects

namespace LF

-- #################################################################
-- * Induction Principles
-- #################################################################

-- =================================================================
-- ** Basics
-- =================================================================

-- In Lean 4, induction principles are automatically generated for
-- every inductive datatype. For the type Nat, the principle is Nat.rec.

#check Nat.rec
/-
Nat.rec.{u} {motive : Nat → Sort u} (zero : motive Nat.zero)
  (succ : (n : Nat) → motive n → motive (Nat.succ n)) (t : Nat) : motive t
-/

-- This matches nat_ind from Coq, but motive can be in Sort u (Prop, Type, etc.)
-- When motive : Nat → Prop, it is exactly nat_ind.

-- We can use Nat.rec or Nat.recOn to perform induction manually.
-- Here is mul_0_r' using Nat.recOn.
-- Note: In Lean's standard library, Nat.mul is defined by matching on the second
-- argument, so n * 0 = 0 is true by definition (rfl). To make the induction
-- example meaningful and similar to Coq, we'll prove 0 * n = 0.

theorem mul_0_r' : ∀ n : Nat, 0 * n = 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n' IHn' =>
    simp [Nat.mul_succ, IHn']

-- **** Exercise: 2 stars, standard (plus_one_r')
-- Complete this proof without using the induction tactic.
theorem plus_one_r' : ∀ n : Nat, n + 1 = Nat.succ n := by
  sorry

-- Non-recursive datatypes also get induction principles.

inductive time : Type where
  | day
  | night

#check time.rec
/-
time.rec.{u} {motive : time → Sort u} (day : motive time.day)
  (night : motive time.night) (t : time) : motive t
-/

-- **** Exercise: 1 star, standard, optional (rgb)
-- Write out the induction principle that Lean will generate for the
-- following datatype.

inductive rgb : Type where
  | red
  | green
  | blue

#check rgb.rec

-- #################################################################
-- * Induction Principles for Recursive Types
-- #################################################################

inductive natlist : Type where
  | nnil
  | ncons (n : Nat) (l : natlist)

#check natlist.rec
/-
natlist.rec.{u} {motive : natlist → Sort u} (nnil : motive natlist.nnil)
  (ncons : (n : Nat) → (l : natlist) → motive l → motive (natlist.ncons n l))
  (t : natlist) : motive t
-/

inductive natlist' : Type where
  | nnil'
  | nsnoc (l : natlist') (n : Nat)

#check natlist'.rec

-- **** Exercise: 2 stars, standard (booltree_ind)
inductive booltree : Type where
  | bt_empty
  | bt_leaf (b : Bool)
  | bt_branch (b : Bool) (t1 t2 : booltree)

def booltree_property_type : Type := booltree → Prop

def base_case (P : booltree_property_type) : Prop :=
  sorry

def leaf_case (P : booltree_property_type) : Prop :=
  sorry

def branch_case (P : booltree_property_type) : Prop :=
  sorry

def booltree_ind_type :=
  ∀ (P : booltree_property_type),
    base_case P →
    leaf_case P →
    branch_case P →
    ∀ (b : booltree), P b

theorem booltree_ind_type_correct : booltree_ind_type := by
  sorry

-- **** Exercise: 2 stars, standard (toy_ind)
inductive Toy : Type where
  | con1 (b : Bool)
  | con2 (n : Nat) (t : Toy)

theorem Toy_correct : ∃ (f : Bool → Toy) (g : Nat → Toy → Toy),
  ∀ P : Toy → Prop,
    (∀ b : Bool, P (f b)) →
    (∀ (n : Nat) (t : Toy), P t → P (g n t)) →
    ∀ t : Toy, P t := by
  exists Toy.con1, Toy.con2
  intros P H1 H2 t
  induction t with
  | con1 b => apply H1
  | con2 n t' IH => apply H2; exact IH

-- #################################################################
-- * Polymorphism
-- #################################################################

-- Polymorphic lists
inductive list (X : Type) : Type where
  | nil : list X
  | cons : X → list X → list X

#check list.rec

-- **** Exercise: 1 star, standard, optional (tree)
inductive tree (X : Type) : Type where
  | leaf (x : X)
  | node (t1 t2 : tree X)

#check tree.rec

-- **** Exercise: 1 star, standard, optional (mytype)
inductive mytype (X : Type) : Type where
  | constr1 : X → mytype X
  | constr2 : Nat → mytype X
  | constr3 : mytype X → Nat → mytype X

#check mytype.rec

-- **** Exercise: 1 star, standard, optional (foo)
inductive foo_ind (X Y : Type) : Type where
  | bar : X → foo_ind X Y
  | baz : Y → foo_ind X Y
  | quux : (Nat → foo_ind X Y) → foo_ind X Y

#check foo_ind.rec

-- **** Exercise: 1 star, standard, optional (foo')
inductive foo' (X : Type) : Type where
  | C1 (l : List X) (f : foo' X)
  | C2

#check foo'.rec

-- #################################################################
-- * Induction Hypotheses
-- #################################################################

def P_m0r (n : Nat) : Prop :=
  n * 0 = 0

def P_m0r' : Nat → Prop :=
  fun n => n * 0 = 0

theorem mul_0_r'' : ∀ n : Nat, P_m0r n := by
  intro n
  apply Nat.recOn (motive := P_m0r) n
  . -- n = 0
    rfl
  . -- n = S n'
    intros n' IHn'
    unfold P_m0r at IHn'
    unfold P_m0r
    -- n' * 0 = 0 -> (n' + 1) * 0 = 0
    -- In Lean, (n' + 1) * 0 = 0 is rfl.
    rfl

-- #################################################################
-- * More on the induction Tactic
-- #################################################################

theorem add_assoc' : ∀ n m p : Nat,
  n + (m + p) = (n + m) + p := by
  intros n m p
  induction n with
  | zero =>
    rw [Nat.zero_add, Nat.zero_add]
  | succ n' IHn' =>
    rw [Nat.succ_add, Nat.succ_add, Nat.succ_add, IHn']

theorem add_comm' : ∀ n m : Nat,
  n + m = m + n := by
  intros n m
  induction n with
  | zero =>
    rw [Nat.zero_add, Nat.add_zero]
  | succ n' IHn' =>
    rw [Nat.succ_add, IHn', Nat.add_succ]

theorem add_comm'' : ∀ n m : Nat,
  n + m = m + n := by
  intros n m
  induction m with
  | zero =>
    rw [Nat.add_zero, Nat.zero_add]
  | succ m' IHm' =>
    -- n + (m' + 1) = (m' + 1) + n
    -- succ (n + m') = succ (m' + n)
    rw [Nat.add_succ, Nat.succ_add, IHm']

-- **** Exercise: 1 star, standard, optional (plus_explicit_prop)
-- State the theorem and proof in terms of an explicit defined proposition.
-- (Skipped, keeping it as a placeholder for the user to see what's expected)

-- #################################################################
-- * Induction Principles for Propositions
-- #################################################################

namespace PropInduction

open LF.IndProp

#check ev.rec

inductive ev' : Nat → Prop where
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m : ev' n → ev' m → ev' (n + m)

theorem ev_ev' : ∀ n, ev n → ev' n := by
  intros n H
  apply ev.rec (motive := fun n _ => ev' n)
  . -- ev_0
    apply ev'.ev'_0
  . -- ev_SS
    intros m Hm IH
    -- motive (m + 2) (ev.ev_SS m Hm)
    -- In Lean, Nat.add matches second arg, so m + 2 = succ (succ m).
    have H2 : ev' 2 := ev'.ev'_2
    have Hsum := ev'.ev'_sum 2 m H2 IH
    -- 2 + m = m + 2
    rw [Nat.add_comm] at Hsum
    exact Hsum
  . exact H

inductive le1 : Nat → Nat → Prop where
  | le1_n : ∀ n, le1 n n
  | le1_S : ∀ n m, le1 n m → le1 n (Nat.succ m)

inductive le2 (n : Nat) : Nat → Prop where
  | le2_n : le2 n n
  | le2_S : ∀ m, le2 n m → le2 n (Nat.succ m)

#check le1.rec
#check le2.rec

end PropInduction

-- #################################################################
-- * Formal vs. Informal Proofs by Induction
-- #################################################################

-- (Text only section, no code to translate)

-- #################################################################
-- * Explicit Proof Objects for Induction (Optional)
-- #################################################################

#check Nat.rec

def build_proof
    (P : Nat → Prop)
    (evPO : P 0)
    (evPS : ∀ n : Nat, P n → P (Nat.succ n))
    (n : Nat) : P n :=
  match n with
  | 0 => evPO
  | Nat.succ k => evPS k (build_proof P evPO evPS k)

def nat_ind_tidy := build_proof

open LF.IndProp

-- Lemma even_ev : ∀ n : Nat, even n = true → ev n.
-- Attempt to prove with standard induction on n fails.

def nat_ind2 :
  ∀ (P : Nat → Prop),
  P 0 →
  P 1 →
  (∀ n : Nat, P n → P (n + 2)) →
  ∀ n : Nat, P n :=
  fun P P0 P1 PSS =>
    let rec f (n : Nat) : P n :=
      match n with
      | 0 => P0
      | 1 => P1
      | n' + 2 => PSS n' (f n')
    f

-- Using standard 'even' from Basics
open LF (even)

theorem even_ev : ∀ n, even n = true → ev n :=
  nat_ind2 (fun n => even n = true → ev n)
    (fun _ => ev.ev_0)
    (fun H => by simp [even] at H; contradiction)
    (fun n' IH H => by
      simp [even] at H
      apply ev.ev_SS
      apply IH
      exact H)

-- **** Exercise: 4 stars, standard, optional (t_tree)
inductive t_tree (X : Type) : Type where
  | t_leaf : t_tree X
  | t_branch : (t_tree X × X × t_tree X) → t_tree X

def reflect {X : Type} (t : t_tree X) : t_tree X :=
  match t with
  | .t_leaf => .t_leaf
  | .t_branch (l, v, r) => .t_branch (reflect r, v, reflect l)

def better_t_tree_ind_type : Prop :=
  sorry

def better_t_tree_ind : sorry :=
  sorry

theorem reflect_involution : ∀ (X : Type) (t : t_tree X),
    reflect (reflect t) = t := by
  sorry

end LF
