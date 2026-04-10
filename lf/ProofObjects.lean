import lf.IndProp

namespace LF
namespace ProofObjects

open LF.IndProp

-- #################################################################
-- * Proof Objects: The Curry-Howard Correspondence
-- #################################################################

-- =================================================================
-- ** The Curry-Howard Correspondence
-- =================================================================

-- In Lean, we can check the type of ev.ev_0 and ev.ev_SS:
#check ev.ev_0
#check ev.ev_SS
-- ev.ev_SS : ∀ (n : Nat), ev n → ev (n + 2)

-- Now let's look again at an earlier proof involving ev.
theorem ev_4 : ev 4 := by
  apply ev.ev_SS
  apply ev.ev_SS
  apply ev.ev_0

-- We can use #print to see the proof object.
#print ev_4
-- ev_4 = ev.ev_SS 2 (ev.ev_SS 0 ev.ev_0)

-- We can also write down this proof object directly:
#check (ev.ev_SS 2 (ev.ev_SS 0 ev.ev_0))

-- #################################################################
-- * Proof Scripts
-- #################################################################

theorem ev_4' : ev 4 := by
  apply (ev.ev_SS 2 (ev.ev_SS 0 ev.ev_0))

def ev_4'' : ev 4 :=
  ev.ev_SS 2 (ev.ev_SS 0 ev.ev_0)

-- **** Exercise: 2 stars, standard (eight_is_even)
theorem ev_8 : ev 8 := by
  sorry

def ev_8' : ev 8 :=
  sorry

-- #################################################################
-- * Quantifiers, Implications, Functions
-- #################################################################

-- We use n + 4 instead of 4 + n to match Lean's Nat.add definition better,
-- or we would need to use 'omega' or 'rw [Nat.add_comm]' to prove 4 + n = n + 4.
theorem ev_plus4 : ∀ n, ev n → ev (n + 4) := by
  intros n H
  apply ev.ev_SS
  apply ev.ev_SS
  apply H

def ev_plus4' : ∀ n, ev n → ev (n + 4) :=
  fun (n : Nat) => fun (H : ev n) =>
    ev.ev_SS (n + 2) (ev.ev_SS n H)

def ev_plus4'' (n : Nat) (H : ev n) : ev (n + 4) :=
  ev.ev_SS (n + 2) (ev.ev_SS n H)

#check ev_plus4''

def ev_plus2 : Prop :=
  ∀ n, ∀ (E : ev n), ev (n + 2)

def ev_plus2' : Prop :=
  ∀ n, ∀ (_ : ev n), ev (n + 2)

def ev_plus2'' : Prop :=
  ∀ n, ev n → ev (n + 2)

-- #################################################################
-- * Programming with Tactics
-- #################################################################

def add2 : Nat → Nat := by
  intro n
  apply Nat.succ
  apply Nat.succ
  exact n

#print add2

#eval add2 2
-- 4

-- #################################################################
-- * Logical Connectives as Inductive Types
-- #################################################################

namespace Props

-- =================================================================
-- ** Conjunction
-- =================================================================

namespace And

inductive and (P Q : Prop) : Prop where
  | conj : P → Q → and P Q

-- proj1'
theorem proj1' : ∀ P Q, and P Q → P := by
  intros P Q HPQ
  cases HPQ with
  | conj HP HQ => exact HP

theorem and_comm : ∀ P Q : Prop, (and P Q) ↔ (and Q P) := by
  intros P Q
  apply Iff.intro
  . intro H
    cases H with
    | conj HP HQ => exact and.conj HQ HP
  . intro H
    cases H with
    | conj HQ HP => exact and.conj HP HQ

def proj1'' P Q (HPQ : and P Q) : P :=
  match HPQ with
  | and.conj HP HQ => HP

def and_comm'_aux P Q (H : and P Q) : and Q P :=
  match H with
  | and.conj HP HQ => and.conj HQ HP

def and_comm' P Q : (and P Q) ↔ (and Q P) :=
  Iff.intro (and_comm'_aux P Q) (and_comm'_aux Q P)

-- **** Exercise: 2 stars, standard (conj_fact)
def conj_fact : ∀ P Q R, and P Q → and Q R → and P R :=
  sorry

end And

-- =================================================================
-- ** Disjunction
-- =================================================================

namespace Or

inductive or (P Q : Prop) : Prop where
  | or_introl : P → or P Q
  | or_intror : Q → or P Q

def inj_l : ∀ (P Q : Prop), P → or P Q :=
  fun P Q HP => or.or_introl HP

theorem inj_l' : ∀ (P Q : Prop), P → or P Q := by
  intros P Q HP
  apply or.or_introl
  exact HP

def or_elim : ∀ (P Q R : Prop), (or P Q) → (P → R) → (Q → R) → R :=
  fun P Q R HPQ HPR HQR =>
    match HPQ with
    | or.or_introl HP => HPR HP
    | or.or_intror HQ => HQR HQ

theorem or_elim' : ∀ (P Q R : Prop), (or P Q) → (P → R) → (Q → R) → R := by
  intros P Q R HPQ HPR HQR
  cases HPQ with
  | or_introl HP => apply HPR; exact HP
  | or_intror HQ => apply HQR; exact HQ

-- **** Exercise: 2 stars, standard (or_commut')
def or_commut' : ∀ P Q, or P Q → or Q P :=
  sorry

end Or

-- =================================================================
-- ** Existential Quantification
-- =================================================================

namespace Ex

inductive ex {A : Type} (P : A → Prop) : Prop where
  | ex_intro : ∀ x : A, P x → ex P

def some_nat_is_even : ex (fun n => ev n) :=
  ex.ex_intro 4 (ev.ev_SS 2 (ev.ev_SS 0 ev.ev_0))

-- **** Exercise: 2 stars, standard (ex_ev_Sn)
def ex_ev_Sn : ex (fun n => ev (Nat.succ n)) :=
  sorry

def dist_exists_or_term (X:Type) (P Q : X → Prop) :
  (ex (fun x => (Or.or (P x) (Q x)))) → (Or.or (ex P) (ex Q)) :=
  fun H => match H with
           | ex.ex_intro x Hx =>
               match Hx with
               | Or.or.or_introl HPx => Or.or.or_introl (ex.ex_intro x HPx)
               | Or.or.or_intror HQx => Or.or.or_intror (ex.ex_intro x HQx)

-- **** Exercise: 2 stars, standard (ex_match)
def ex_match : ∀ (A : Type) (P Q : A → Prop),
  (∀ x, P x → Q x) →
  (ex P) → (ex Q) :=
  sorry

end Ex

-- =================================================================
-- ** [True] and [False]
-- =================================================================

inductive True : Prop where
  | I : True

-- **** Exercise: 1 star, standard (p_implies_true)
def p_implies_true : ∀ P, P → True :=
  sorry

inductive False : Prop where

-- false_implies_zero_eq_one
def false_implies_zero_eq_one : False → 0 = 1 :=
  fun contra => nomatch contra

-- **** Exercise: 1 star, standard (ex_falso_quodlibet')
def ex_falso_quodlibet' : ∀ P, False → P :=
  sorry

end Props

-- #################################################################
-- * Equality
-- #################################################################

namespace EqualityPlayground

inductive eq {X : Type} (x : X) : X → Prop where
  | eq_refl : eq x x

-- Precedence of === should be lower than + (which is 65).
-- We use === to avoid ambiguity with Lean's built-in == (BEq.beq).
local notation:50 x " === " y => eq x y

theorem four: (2 + 2) === (1 + 3) :=
  eq.eq_refl

def four' : (2 + 2) === (1 + 3) :=
  eq.eq_refl

def singleton : ∀ (X:Type) (x:X), ([] ++ [x]) === (x :: []) :=
  fun _ _ => eq.eq_refl

def eq_add : ∀ (n1 n2 : Nat), (eq n1 n2) → (eq (Nat.succ n1) (Nat.succ n2)) :=
  fun n1 _ Heq =>
    match Heq with
    | eq.eq_refl => eq.eq_refl

theorem eq_add' : ∀ (n1 n2 : Nat), (eq n1 n2) → (eq (Nat.succ n1) (Nat.succ n2)) := by
  intros n1 n2 Heq
  cases Heq with
  | eq_refl => apply eq.eq_refl

-- **** Exercise: 2 stars, standard (eq_cons)
def eq_cons : ∀ (X : Type) (h1 h2 : X) (t1 t2 : List X),
    (eq h1 h2) → (eq t1 t2) → (eq (h1 :: t1) (h2 :: t2)) :=
  sorry

-- **** Exercise: 2 stars, standard (equality__leibniz_equality)
theorem equality__leibniz_equality : ∀ (X : Type) (x y: X),
  (eq x y) → ∀ (P : X → Prop), P x → P y :=
  sorry

-- **** Exercise: 2 stars, standard (equality__leibniz_equality_term)
def equality__leibniz_equality_term : ∀ (X : Type) (x y: X),
    (eq x y) → ∀ P : (X → Prop), P x → P y :=
  sorry

-- **** Exercise: 3 stars, standard, optional (leibniz_equality__equality)
theorem leibniz_equality__equality : ∀ (X : Type) (x y: X),
  (∀ P:X→Prop, P x → P y) → (eq x y) :=
  sorry

end EqualityPlayground

-- #################################################################
-- * Rocq's Trusted Computing Base
-- #################################################################

/-
One question that arises with any automated proof assistant
is "why should we trust it?" -- i.e., what if there is a bug in
the implementation that renders all its reasoning suspect?

While it is impossible to allay such concerns completely, the fact
that Rocq is based on the Curry-Howard correspondence gives it a
strong foundation. Because propositions are just types and proofs
are just terms, checking that an alleged proof of a proposition is
valid just amounts to _type-checking_ the term.
-/

/-
def or_bogus : ∀ P Q, P ∨ Q → P :=
  fun (P Q : Prop) (A : P ∨ Q) =>
    match A with
    | Or.inl H => H
-/
-- Lean's exhaustiveness check will reject this.

/-
partial def infinite_loop {X : Type} (n : Nat) : X :=
  infinite_loop n

def falso : False := infinite_loop 0
-/
-- Lean requires 'partial' for non-terminating functions, and partial functions
-- cannot be used to prove propositions in Prop.

-- #################################################################
-- * More Exercises
-- #################################################################

-- **** Exercise: 2 stars, standard (and_assoc)
def and_assoc : ∀ P Q R : Prop,
    P ∧ (Q ∧ R) → (P ∧ Q) ∧ R :=
  sorry

-- **** Exercise: 3 stars, standard (or_distributes_over_and)
def or_distributes_over_and : ∀ P Q R : Prop,
    P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) :=
  sorry

-- **** Exercise: 3 stars, standard (negations)
def double_neg : ∀ P : Prop,
    P → ¬¬P :=
  sorry

def contradiction_implies_anything : ∀ P Q : Prop,
    (P ∧ ¬P) → Q :=
  sorry

def de_morgan_not_or : ∀ P Q : Prop,
    ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
  sorry

-- **** Exercise: 2 stars, standard (currying)
def curry : ∀ P Q R : Prop,
    ((P ∧ Q) → R) → (P → (Q → R)) :=
  sorry

def uncurry : ∀ P Q R : Prop,
    (P → (Q → R)) → ((P ∧ Q) → R) :=
  sorry

-- #################################################################
-- * Proof Irrelevance (Advanced)
-- #################################################################

def propositional_extensionality : Prop :=
  ∀ (P Q : Prop), (P ↔ Q) → P = Q

-- **** Exercise: 1 star, advanced (pe_implies_or_eq)
theorem pe_implies_or_eq :
  propositional_extensionality →
  ∀ (P Q : Prop), (P ∨ Q) = (Q ∨ P) :=
  sorry

-- **** Exercise: 1 star, advanced (pe_implies_true_eq)
theorem pe_implies_true_eq :
  propositional_extensionality →
  ∀ (P : Prop), P → True = P :=
  sorry

def proof_irrelevance : Prop :=
  ∀ (P : Prop) (pf1 pf2 : P), pf1 = pf2

-- **** Exercise: 3 stars, advanced (pe_implies_pi)
theorem pe_implies_pi :
  propositional_extensionality → proof_irrelevance :=
  sorry

end ProofObjects
end LF
