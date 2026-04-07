import lf.Logic

namespace LF
namespace IndProp

-- #################################################################
-- * Inductively Defined Propositions
-- #################################################################

-- =================================================================
-- ** Example: The Collatz Conjecture
-- =================================================================

def div2 (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | n' + 2 => (div2 n') + 1

def even (n : Nat) : Bool :=
  match n with
  | 0 => true
  | 1 => false
  | n' + 2 => even n'

def csf (n : Nat) : Nat :=
  if even n then div2 n
  else (3 * n) + 1

inductive Collatz_holds_for : Nat → Prop where
  | Chf_one : Collatz_holds_for 1
  | Chf_even (n : Nat) : even n = true →
                         Collatz_holds_for (div2 n) →
                         Collatz_holds_for n
  | Chf_odd (n : Nat) :  even n = false →
                         Collatz_holds_for ((3 * n) + 1) →
                         Collatz_holds_for n

example : Collatz_holds_for 12 := by
  apply Collatz_holds_for.Chf_even; rfl
  apply Collatz_holds_for.Chf_even; rfl
  apply Collatz_holds_for.Chf_odd; rfl
  apply Collatz_holds_for.Chf_even; rfl
  apply Collatz_holds_for.Chf_odd; rfl
  apply Collatz_holds_for.Chf_even; rfl
  apply Collatz_holds_for.Chf_even; rfl
  apply Collatz_holds_for.Chf_even; rfl
  apply Collatz_holds_for.Chf_even; rfl
  apply Collatz_holds_for.Chf_one

axiom collatz : ∀ n, n ≠ 0 → Collatz_holds_for n

-- =================================================================
-- ** Example: Binary relation for comparing numbers
-- =================================================================

namespace LePlayground

inductive le_custom : Nat → Nat → Prop where
  | le_n (n : Nat)   : le_custom n n
  | le_S (n m : Nat) : le_custom n m → le_custom n (Nat.succ m)

example : le_custom 3 5 := by
  apply le_custom.le_S
  apply le_custom.le_S
  apply le_custom.le_n

end LePlayground

-- =================================================================
-- ** Example: Transitive Closure
-- =================================================================

inductive clos_trans {X: Type} (R: X → X → Prop) : X → X → Prop where
  | t_step (x y : X) :
      R x y →
      clos_trans R x y
  | t_trans (x y z : X) :
      clos_trans R x y →
      clos_trans R y z →
      clos_trans R x z

inductive Person : Type where
  | Sage : Person
  | Cleo : Person
  | Ridley : Person
  | Moss : Person

inductive parent_of : Person → Person → Prop where
  | po_SC : parent_of Person.Sage Person.Cleo
  | po_SR : parent_of Person.Sage Person.Ridley
  | po_CM : parent_of Person.Cleo Person.Moss

def ancestor_of (p1 p2 : Person) : Prop :=
  clos_trans parent_of p1 p2

example : ancestor_of Person.Sage Person.Moss := by
  unfold ancestor_of
  apply clos_trans.t_trans (y := Person.Cleo)
  . apply clos_trans.t_step
    apply parent_of.po_SC
  . apply clos_trans.t_step
    apply parent_of.po_CM

-- =================================================================
-- ** Example: Reflexive and Transitive Closure
-- =================================================================

inductive clos_refl_trans {X: Type} (R: X → X → Prop) : X → X → Prop where
  | rt_step (x y : X) :
      R x y →
      clos_refl_trans R x y
  | rt_refl (x : X) :
      clos_refl_trans R x x
  | rt_trans (x y z : X) :
      clos_refl_trans R x y →
      clos_refl_trans R y z →
      clos_refl_trans R x z

def cs (n m : Nat) : Prop := csf n = m

def cms (n m : Nat) : Prop := clos_refl_trans cs n m

axiom collatz' : ∀ n, n ≠ 0 → cms n 1

-- =================================================================
-- ** Example: Permutations
-- =================================================================

inductive Perm3 {X : Type} : List X → List X → Prop where
  | perm3_swap12 (a b c : X) :
      Perm3 [a,b,c] [b,a,c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a,b,c] [a,c,b]
  | perm3_trans (l1 l2 l3 : List X) :
      Perm3 l1 l2 → Perm3 l2 l3 → Perm3 l1 l3

-- =================================================================
-- ** Example: Evenness (yet again)
-- =================================================================

inductive ev : Nat → Prop where
  | ev_0                       : ev 0
  | ev_SS (n : Nat) (H : ev n) : ev (Nat.succ (Nat.succ n))

theorem ev_4 : ev 4 := by
  apply ev.ev_SS
  apply ev.ev_SS
  apply ev.ev_0

theorem ev_4' : ev 4 :=
  ev.ev_SS 2 (ev.ev_SS 0 ev.ev_0)

theorem ev_plus4 : ∀ n, ev n → ev (4 + n) := by
  intros n Hn
  replace Hn : ev n := Hn
  have h1 : 4 + n = Nat.succ (Nat.succ (Nat.succ (Nat.succ n))) := by omega
  rw [h1]
  apply ev.ev_SS
  apply ev.ev_SS
  exact Hn

-- #################################################################
-- * Using Evidence in Proofs
-- #################################################################

-- =================================================================
-- ** Destructing and Inverting Evidence
-- =================================================================

theorem ev_inversion : ∀ (n : Nat),
    ev n →
    (n = 0) ∨ (∃ n', n = Nat.succ (Nat.succ n') ∧ ev n') := by
  intros n E
  cases E with
  | ev_0 => exact Or.inl rfl
  | ev_SS n' E' => exact Or.inr ⟨n', rfl, E'⟩

theorem evSS_ev : ∀ n, ev (Nat.succ (Nat.succ n)) → ev n := by
  intros n E
  have H := ev_inversion (Nat.succ (Nat.succ n)) E
  cases H with
  | inl h0 => contradiction
  | inr h1 =>
    let ⟨n', h2, E'⟩ := h1
    injection h2 with hnn'
    injection hnn' with hnn''
    rewrite [hnn'']
    exact E'

theorem evSS_ev' : ∀ n, ev (Nat.succ (Nat.succ n)) → ev n := by
  intros n E
  cases E with
  | ev_SS n' E' => exact E'

theorem one_not_even : ¬ ev 1 := by
  intro H; cases H

theorem one_not_even' : ¬ ev 1 := by
  intro H; cases H

theorem inversion_ex1 : ∀ (n m o : Nat),
  [n, m] = [o, o] → [n] = [m] := by
  intros n m o H
  injection H with h1 h2
  rewrite [h1, h2]
  rfl

theorem inversion_ex2 : ∀ (n : Nat),
  Nat.succ n = 0 → 2 + 2 = 5 := by
  intros n contra; contradiction

-- =================================================================
-- ** Induction on Evidence
-- =================================================================

theorem ev_Even : ∀ n, ev n → LF.Logic.Even n := by
  intros n E
  induction E with
  | ev_0 => exact ⟨0, rfl⟩
  | ev_SS n' _ IH =>
    let ⟨k, Hk⟩ := IH
    exact ⟨k + 1, by omega⟩

theorem ev_Even_iff : ∀ n, ev n ↔ LF.Logic.Even n := by
  intros n
  constructor
  . exact ev_Even n
  . intro _
    sorry

-- =================================================================
-- ** Multiple Induction Hypotheses
-- =================================================================

namespace clos_refl_trans_remainder
inductive clos_refl_trans {X: Type} (R: X → X → Prop) : X → X → Prop where
  | rt_step (x y : X) :
      R x y →
      clos_refl_trans R x y
  | rt_refl (x : X) :
      clos_refl_trans R x x
  | rt_trans (x y z : X) :
      clos_refl_trans R x y →
      clos_refl_trans R y z →
      clos_refl_trans R x z
end clos_refl_trans_remainder

def isDiagonal {X : Type} (R: X → X → Prop) :=
  ∀ x y, R x y → x = y

theorem closure_of_diagonal_is_diagonal: ∀ X (R: X → X → Prop),
  isDiagonal R →
  isDiagonal (clos_refl_trans_remainder.clos_refl_trans R) := by
  intros X R IsDiag x y H
  induction H with
  | rt_step _ _ H' => apply IsDiag; exact H'
  | rt_refl _ => rfl
  | rt_trans _ _ _ _ _ IH1 IH2 =>
    rewrite [IH1, IH2]; rfl

namespace Perm3Reminder
inductive Perm3 {X : Type} : List X → List X → Prop where
  | perm3_swap12 (a b c : X) :
      Perm3 [a, b, c] [b, a, c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a, b, c] [a, c, b]
  | perm3_trans (l1 l2 l3 : List X) :
      Perm3 l1 l2 → Perm3 l2 l3 → Perm3 l1 l3
end Perm3Reminder

theorem Perm3_symm : ∀ (X : Type) (l1 l2 : List X),
  Perm3Reminder.Perm3 l1 l2 → Perm3Reminder.Perm3 l2 l1 := by
  intros X l1 l2 E
  induction E with
  | perm3_swap12 a b c => apply Perm3Reminder.Perm3.perm3_swap12
  | perm3_swap23 a b c => apply Perm3Reminder.Perm3.perm3_swap23
  | perm3_trans _ _ _ _ _ IH12 IH23 =>
    exact Perm3Reminder.Perm3.perm3_trans _ _ _ IH23 IH12

-- #################################################################
-- * Exercising with Inductive Relations
-- #################################################################

namespace Playground

inductive le_custom : Nat → Nat → Prop where
  | le_n (n : Nat)                : le_custom n n
  | le_S (n m : Nat) (H : le_custom n m) : le_custom n (Nat.succ m)

theorem test_le1 :
  le_custom 3 3 := by
  apply le_custom.le_n

theorem test_le2 :
  le_custom 3 6 := by
  apply le_custom.le_S
  apply le_custom.le_S
  apply le_custom.le_S
  apply le_custom.le_n

theorem test_le3 :
  (le_custom 2 1) → 2 + 2 = 5 := by
  intro H
  cases H with
  | le_S _ H' => cases H'

def lt (n m : Nat) := le_custom (Nat.succ n) m
def ge (m n : Nat) : Prop := le_custom n m

end Playground

-- #################################################################
-- * Case Study: Regular Expressions
-- #################################################################

inductive reg_exp (T : Type) : Type where
  | EmptySet : reg_exp T
  | EmptyStr : reg_exp T
  | Char : T → reg_exp T
  | App : reg_exp T → reg_exp T → reg_exp T
  | Union : reg_exp T → reg_exp T → reg_exp T
  | Star : reg_exp T → reg_exp T

inductive exp_match {T : Type} : List T → reg_exp T → Prop where
  | MEmpty : exp_match [] reg_exp.EmptyStr
  | MChar (x : T) : exp_match [x] (reg_exp.Char x)
  | MApp (s1 : List T) (re1 : reg_exp T) (s2 : List T) (re2 : reg_exp T)
             (H1 : exp_match s1 re1)
             (H2 : exp_match s2 re2)
           : exp_match (s1 ++ s2) (reg_exp.App re1 re2)
  | MUnionL (s1 : List T) (re1 re2 : reg_exp T)
                (H1 : exp_match s1 re1)
              : exp_match s1 (reg_exp.Union re1 re2)
  | MUnionR (s2 : List T) (re1 re2 : reg_exp T)
                (H2 : exp_match s2 re2)
              : exp_match s2 (reg_exp.Union re1 re2)
  | MStar0 (re : reg_exp T) : exp_match [] (reg_exp.Star re)
  | MStarApp (s1 s2 : List T) (re : reg_exp T)
                 (H1 : exp_match s1 re)
                 (H2 : exp_match s2 (reg_exp.Star re))
               : exp_match (s1 ++ s2) (reg_exp.Star re)

example : exp_match [1] (reg_exp.Char 1) := by
  apply exp_match.MChar

-- #################################################################
-- * Case Study: Improving Reflection
-- #################################################################

inductive reflect (P : Prop) : Bool → Prop where
  | ReflectT (H :   P) : reflect P true
  | ReflectF (H : ¬ P) : reflect P false

theorem iff_reflect : ∀ P b, (P ↔ b = true) → reflect P b := by
  intros P b H
  cases b with
  | true => exact reflect.ReflectT (H.mpr rfl)
  | false => exact reflect.ReflectF (fun h => Bool.noConfusion (H.mp h))

theorem eqbP : ∀ (n m : Nat), reflect (n = m) (n == m) := by
  intros n m
  apply iff_reflect
  exact beq_iff_eq.symm

-- #################################################################
-- * Additional Exercises (keep sorry)
-- #################################################################

theorem ev_double : ∀ n, ev (2 * n) := by sorry
theorem Perm3_ex1 : Perm3Reminder.Perm3 [1, 2, 3] [2, 3, 1] := by sorry
theorem Perm3_refl : ∀ (X : Type) (a b c : X), Perm3Reminder.Perm3 [a, b, c] [a, b, c] := by sorry
theorem SSSSev__even : ∀ n, ev (Nat.succ (Nat.succ (Nat.succ (Nat.succ n)))) → ev n := by sorry
theorem ev5_nonsense : ev 5 → 2 + 2 = 9 := by sorry
theorem le_trans : ∀ m n o, Playground.le_custom m n → Playground.le_custom n o → Playground.le_custom m o := by sorry
theorem O_le_n : ∀ n, Playground.le_custom 0 n := by sorry
theorem n_le_m__Sn_le_Sm : ∀ n m, Playground.le_custom n m → Playground.le_custom (Nat.succ n) (Nat.succ m) := by sorry
theorem Sn_le_Sm__n_le_m : ∀ n m, Playground.le_custom (Nat.succ n) (Nat.succ m) → Playground.le_custom n m := by sorry
theorem le_plus_l : ∀ a b, Playground.le_custom a (a + b) := by sorry
theorem plus_le : ∀ n1 n2 m, Playground.le_custom (n1 + n2) m → Playground.le_custom n1 m ∧ Playground.le_custom n2 m := by sorry
theorem plus_le_cases : ∀ n m p q, Playground.le_custom (n + m) (p + q) → Playground.le_custom n p ∨ Playground.le_custom m q := by sorry
theorem plus_le_compat_l : ∀ n m p, Playground.le_custom n m → Playground.le_custom (p + n) (p + m) := by sorry
theorem plus_le_compat_r : ∀ n m p, Playground.le_custom n m → Playground.le_custom (n + p) (m + p) := by sorry
theorem le_plus_trans : ∀ n m p, Playground.le_custom n m → Playground.le_custom n (m + p) := by sorry
theorem lt_ge_cases : ∀ n m, Playground.lt n m ∨ Playground.ge n m := by sorry
theorem n_lt_m__n_le_m : ∀ n m, Playground.lt n m → Playground.le_custom n m := by sorry
theorem plus_lt : ∀ n1 n2 m, Playground.lt (n1 + n2) m → Playground.lt n1 m ∧ Playground.lt n2 m := by sorry
theorem leb_complete : ∀ (n m : Nat), (n == m) = true → Playground.le_custom n m := by sorry
theorem leb_correct : ∀ (n m : Nat), Playground.le_custom n m → (n == m) = true := by sorry
theorem leb_iff : ∀ (n m : Nat), (n == m) = true ↔ Playground.le_custom n m := by sorry
theorem leb_true_trans : ∀ (n m o : Nat), (n == m) = true → (m == o) = true → (n == o) = true := by sorry

namespace R
inductive R_rel : Nat → Nat → Nat → Prop where
  | c1                                     : R_rel 0     0     0
  | c2 m n o (H : R_rel m     n     o        ) : R_rel (Nat.succ m) n     (Nat.succ o)
  | c3 m n o (H : R_rel m     n     o        ) : R_rel m     (Nat.succ n) (Nat.succ o)
  | c4 m n o (H : R_rel (Nat.succ m) (Nat.succ n) (Nat.succ (Nat.succ o))) : R_rel m     n     o
  | c5 m n o (H : R_rel m     n     o        ) : R_rel n     m     o
def fR : Nat → Nat → Nat := sorry
theorem R_equiv_fR : ∀ m n o, R_rel m n o ↔ fR m n = o := by sorry
end R

inductive subseq : List Nat → List Nat → Prop where
  | sub_nil (l : List Nat) : subseq [] l
  | sub_take (x : Nat) (l1 l2 : List Nat) (H : subseq l1 l2) : subseq (x :: l1) (x :: l2)
  | sub_skip (x : Nat) (l1 l2 : List Nat) (H : subseq l1 l2) : subseq l1 (x :: l2)

theorem subseq_refl : ∀ (l : List Nat), subseq l l := by sorry
theorem subseq_app : ∀ (l1 l2 l3 : List Nat), subseq l1 l2 → subseq l1 (l2 ++ l3) := by sorry
theorem subseq_trans : ∀ (l1 l2 l3 : List Nat), subseq l1 l2 → subseq l2 l3 → subseq l1 l3 := by sorry

inductive total_relation : Nat → Nat → Prop where
  | total (n m : Nat) : total_relation n m

theorem total_relation_is_total : ∀ n m, total_relation n m := by sorry

inductive empty_relation : Nat → Nat → Prop where

theorem empty_relation_is_empty : ∀ n m, ¬ empty_relation n m := by sorry

theorem reflect_iff_ex : ∀ P b, reflect P b → (P ↔ b = true) := by sorry

inductive nostutter {X:Type} : List X → Prop where
  | nostutter_nil : nostutter []
  | nostutter_one (x : X) : nostutter [x]
  | nostutter_cons (x y : X) (l : List X) (H1 : x ≠ y) (H2 : nostutter (y :: l)) : nostutter (x :: y :: l)

inductive merge {X:Type} : List X → List X → List X → Prop where
  | merge_nil : merge [] [] []
  | merge_left (x : X) (l1 l2 l : List X) (H : merge l1 l2 l) : merge (x :: l1) l2 (x :: l)
  | merge_right (x : X) (l1 l2 l : List X) (H : merge l1 l2 l) : merge l1 (x :: l2) (x :: l)

inductive pal {X:Type} : List X → Prop where
  | pal_nil : pal []
  | pal_one (x : X) : pal [x]
  | pal_cons (x : X) (l : List X) (H : pal l) : pal (x :: (l ++ [x]))

inductive repeats {X:Type} : List X → Prop where
  | repeats_hd (x : X) (l : List X) (H : x ∈ l) : repeats (x :: l)
  | repeats_tl (x : X) (l : List X) (H : repeats l) : repeats (x :: l)

def match_eps (re: reg_exp Char) : Bool := sorry
def derive (a : Char) (re : reg_exp Char) : reg_exp Char := sorry
def regex_match (s : List Char) (re : reg_exp Char) : Bool :=
  match s with
  | [] => match_eps re
  | _ :: s' => regex_match s' (derive 'x' re) -- simplified for sorry

end IndProp
end LF
