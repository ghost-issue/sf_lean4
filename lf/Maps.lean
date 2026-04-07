import lf.Logic
import lf.IndProp

namespace LF
namespace Maps

-- #################################################################
-- * Identifiers
-- #################################################################

example (x : String) : (x == x) = true := by
  simp

theorem string_beq_refl (x : String) : (x == x) = true := by
  simp

theorem string_beq_eq (n m : String) : (n == m) = true ↔ n = m := by
  exact beq_iff_eq

theorem string_beq_neq (n m : String) : (n == m) = false ↔ n ≠ m := by
  constructor
  . intro h h_eq; rewrite [h_eq] at h; simp at h
  . intro h; apply beq_false_of_ne; exact h

-- #################################################################
-- * Total Maps
-- #################################################################

def total_map (A : Type) := String → A

def t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v)

def t_update {A : Type} (m : total_map A)
                    (x : String) (v : A) :=
  fun x' => if x == x' then v else m x'

-- Notations
notation "empty_map" v => t_empty v
notation x " !-> " v " ; " m => t_update m x v

def examplemap : total_map Bool :=
  ("bar" !-> true ; "foo" !-> true ; empty_map false)

example : examplemap "baz" = false := by rfl
example : examplemap "foo" = true := by rfl
example : examplemap "quux" = false := by rfl
example : examplemap "bar" = true := by rfl

-- =================================================================
-- ** Properties of Total Maps
-- =================================================================

-- Exercise: 1 star, standard, optional (t_apply_empty)
theorem t_apply_empty : ∀ (A : Type) (x : String) (v : A),
  (t_empty v) x = v := by
  sorry

-- Exercise: 2 stars, standard, optional (t_update_eq)
theorem t_update_eq : ∀ (A : Type) (m : total_map A) x v,
  (t_update m x v) x = v := by
  sorry

-- Exercise: 2 stars, standard, optional (t_update_neq)
theorem t_update_neq : ∀ (A : Type) (m : total_map A) x1 x2 v,
  x1 ≠ x2 →
  (t_update m x1 v) x2 = m x2 := by
  sorry

-- Exercise: 2 stars, standard, optional (t_update_shadow)
theorem t_update_shadow : ∀ (A : Type) (m : total_map A) x v1 v2,
  (t_update (t_update m x v1) x v2) = (t_update m x v2) := by
  sorry

-- Exercise: 2 stars, standard (t_update_same)
theorem t_update_same : ∀ (A : Type) (m : total_map A) x,
  (t_update m x (m x)) = m := by
  sorry

-- Exercise: 3 stars, standard, especially useful (t_update_permute)
theorem t_update_permute : ∀ (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
  x2 ≠ x1 →
  (t_update (t_update m x2 v2) x1 v1)
  =
  (t_update (t_update m x1 v1) x2 v2) := by
  sorry

-- #################################################################
-- * Partial maps
-- #################################################################

def partial_map (A : Type) := total_map (Option A)

def empty {A : Type} : partial_map A :=
  t_empty Option.none

def update {A : Type} (m : partial_map A)
           (x : String) (v : A) :=
  t_update m x (Option.some v)

-- Notations for partial maps
notation x " |-> " v " ; " m => update m x v
notation x " |-> " v => update empty x v

def examplepmap : partial_map Bool :=
  ("Church" |-> true ; "Turing" |-> false ; empty)

-- Basic lemmas for partial maps

theorem apply_empty : ∀ (A : Type) (x : String),
  (empty : partial_map A) x = Option.none := by
  intros; unfold empty; rewrite [t_apply_empty]; rfl

theorem update_eq : ∀ (A : Type) (m : partial_map A) x v,
  (update m x v) x = Option.some v := by
  intros; unfold update; rewrite [t_update_eq]; rfl

theorem update_neq : ∀ (A : Type) (m : partial_map A) x1 x2 v,
  x2 ≠ x1 →
  (update m x2 v) x1 = m x1 := by
  intros A m x1 x2 v H; unfold update; rewrite [t_update_neq]
  . rfl
  . exact H

theorem update_shadow : ∀ (A : Type) (m : partial_map A) x v1 v2,
  (update (update m x v1) x v2) = (update m x v2) := by
  intros; unfold update; rewrite [t_update_shadow]; rfl

theorem update_same : ∀ (A : Type) (m : partial_map A) x v,
  m x = Option.some v →
  (update m x v) = m := by
  intros A m x v H; unfold update; rewrite [← H]
  apply t_update_same

theorem update_permute : ∀ (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
  x2 ≠ x1 →
  (update (update m x2 v2) x1 v1) = (update (update m x1 v1) x2 v2) := by
  intros A m x1 x2 v1 v2 H; unfold update
  apply t_update_permute
  exact H

-- #################################################################
-- * Map Inclusion
-- #################################################################

def includedin {A : Type} (m m' : partial_map A) :=
  ∀ x v, m x = Option.some v → m' x = Option.some v

theorem includedin_update : ∀ (A : Type) (m m' : partial_map A)
                                 (x : String) (vx : A),
  includedin m m' →
  includedin (update m x vx) (update m' x vx) := by
  unfold includedin
  intros A m m' x vx H y vy
  unfold update
  unfold t_update
  by_cases hy : x == y
  . simp [hy]
  . simp [hy]
    apply H

-- #################################################################
-- * Exercises (keep empty)
-- #################################################################

end Maps
end LF
