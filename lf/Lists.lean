import lf.Induction

namespace LF
namespace NatList

-- =================================================================
-- Pairs of Numbers
-- =================================================================

inductive NatProd : Type where
  | pair (n1 n2 : Nat)

def fst (p : NatProd) : Nat :=
  match p with
  | .pair x _ => x

def snd (p : NatProd) : Nat :=
  match p with
  | .pair _ y => y

def swap_pair (p : NatProd) : NatProd :=
  match p with
  | .pair x y => .pair y x

theorem surjective_pairing' (n m : Nat) : NatProd.pair n m = NatProd.pair (fst (.pair n m)) (snd (.pair n m)) := by
  rfl

theorem surjective_pairing (p : NatProd) : p = NatProd.pair (fst p) (snd p) := by
  cases p
  rfl

-- Exercise: snd_fst_is_swap (1 star)
theorem snd_fst_is_swap (p : NatProd) : NatProd.pair (snd p) (fst p) = swap_pair p := by
  sorry

-- Exercise: fst_swap_is_snd (1 star)
theorem fst_swap_is_snd (p : NatProd) : fst (swap_pair p) = snd p := by
  sorry

-- =================================================================
-- Lists of Numbers
-- =================================================================

inductive NatList : Type where
  | nil
  | cons (n : Nat) (l : NatList)

-- Introducing notation for lists
local notation "[" "]" => NatList.nil
local infixr:60 " :: " => NatList.cons

def repeat_func (n count : Nat) : NatList :=
  match count with
  | 0 => []
  | count' + 1 => n :: repeat_func n count'

def length (l : NatList) : Nat :=
  match l with
  | [] => 0
  | _ :: t => length t + 1

def app (l1 l2 : NatList) : NatList :=
  match l1 with
  | [] => l2
  | h :: t => h :: app t l2

local infixr:60 " ++ " => app

def hd (default : Nat) (l : NatList) : Nat :=
  match l with
  | [] => default
  | h :: _ => h

def tl (l : NatList) : NatList :=
  match l with
  | [] => []
  | _ :: t => t

-- Exercise: list_funs (2 stars)
def nonzeros (l : NatList) : NatList :=
  sorry

def oddmembers (l : NatList) : NatList :=
  sorry

def countoddmembers (l : NatList) : Nat :=
  sorry

-- Exercise: alternate (3 stars)
def alternate (l1 l2 : NatList) : NatList :=
  sorry

-- Bags via Lists
def Bag := NatList

-- Exercise: bag_functions (3 stars)
def count (v : Nat) (s : Bag) : Nat :=
  sorry

def sum (s1 s2 : Bag) : Bag :=
  sorry

def add (v : Nat) (s : Bag) : Bag :=
  sorry

def member (v : Nat) (s : Bag) : Bool :=
  sorry

-- Exercise: bag_more_functions (3 stars)
def remove_one (v : Nat) (s : Bag) : Bag :=
  sorry

def remove_all (v : Nat) (s : Bag) : Bag :=
  sorry

def included (s1 s2 : Bag) : Bool :=
  sorry

-- Exercise: add_inc_count (2 stars)
theorem add_inc_count (v : Nat) (s : Bag) : count v (add v s) = 1 + count v s := by
  sorry

-- =================================================================
-- Reasoning About Lists
-- =================================================================

theorem nil_app (l : NatList) : [] ++ l = l := by rfl

theorem tl_length_pred (l : NatList) : Nat.pred (length l) = length (tl l) := by
  cases l
  · rfl
  · rfl

-- Induction on Lists
theorem app_assoc (l1 l2 l3 : NatList) : (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) := by
  induction l1 with
  | nil => rfl
  | cons n l1' ih => simp [app, ih]

-- Generalizing Statements
theorem repeat_plus (c1 c2 n : Nat) : repeat_func n c1 ++ repeat_func n c2 = repeat_func n (c1 + c2) := by
  induction c1 with
  | zero => simp [repeat_func, app]
  | succ c1' ih =>
    -- Coq
    -- simp [repeat_func, app]
    -- omega
    have h : c1' + 1 + c2 = c1' + c2 + 1 := by omega
    rw [h]
    simp [repeat_func, app, ih]

-- Reversing a List
def rev (l : NatList) : NatList :=
  match l with
  | [] => []
  | h :: t => rev t ++ (h :: [])

theorem app_length_S (l : NatList) (n : Nat) : length (l ++ (n :: [])) = length l + 1 := by
  induction l with
  | nil => rfl
  | cons m l' ih =>
    simp [app, length]
    rw [ih]

theorem rev_length (l : NatList) : length (rev l) = length l := by
  induction l with
  | nil => rfl
  | cons n l' ih =>
    simp [rev, length]
    rw [app_length_S]
    omega

theorem app_length (l1 l2 : NatList) : length (l1 ++ l2) = length l1 + length l2 := by
  induction l1 with
  -- Coq
  -- nil => rfl
  | nil => simp [length, app]
  | cons n l1' ih =>
    simp [app, length]
    omega

-- =================================================================
-- Search
-- =================================================================
-- #check rev
-- etc.

-- =================================================================
-- List Exercises, Part 1
-- =================================================================

-- Exercise: list_exercises (3 stars)
theorem app_nil_r (l : NatList) : l ++ [] = l := by sorry

theorem rev_app_distr (l1 l2 : NatList) : rev (l1 ++ l2) = rev l2 ++ rev l1 := by sorry

theorem rev_involutive (l : NatList) : rev (rev l) = l := by sorry

theorem app_assoc4 (l1 l2 l3 l4 : NatList) : l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4 := by sorry

theorem nonzeros_app (l1 l2 : NatList) : nonzeros (l1 ++ l2) = nonzeros l1 ++ nonzeros l2 := by sorry

-- Exercise: eqblist (2 stars)
def eqblist (l1 l2 : NatList) : Bool := sorry

theorem eqblist_refl (l : NatList) : true = eqblist l l := by sorry

-- =================================================================
-- List Exercises, Part 2
-- =================================================================

-- Exercise: count_member_nonzero (1 star)
theorem count_member_nonzero (s : Bag) : (1 <=? count 1 (1 :: s)) = true := by sorry

theorem leb_n_Sn (n : Nat) : (n <=? (n + 1)) = true := by
  induction n with
  | zero => rfl
  | succ n' ih => exact ih

-- Exercise: remove_does_not_increase_count (3 stars)
-- Note: we use `<=` directly or via `Nat.ble` since `<=` relates to `Nat.le`
theorem remove_does_not_increase_count (s : Bag) : (count 0 (remove_one 0 s) <=? count 0 s) = true := by sorry

-- Exercise: involution_injective (3 stars)
theorem involution_injective (f : Nat → Nat) (H : ∀ n : Nat, n = f (f n)) : ∀ n1 n2 : Nat, f n1 = f n2 → n1 = n2 := by sorry

-- Exercise: rev_injective (2 stars)
theorem rev_injective (l1 l2 : NatList) : rev l1 = rev l2 → l1 = l2 := by sorry

-- =================================================================
-- Options
-- =================================================================

def nth_bad (l : NatList) (n : Nat) : Nat :=
  match l with
  | [] => 42
  | a :: l' =>
    match n with
    | 0 => a
    | n' + 1 => nth_bad l' n'

inductive NatOption : Type where
  | some (n : Nat)
  | none

def nth_error (l : NatList) (n : Nat) : NatOption :=
  match l with
  | [] => .none
  | a :: l' =>
    match n with
    | 0 => .some a
    | n' + 1 => nth_error l' n'

def option_elim (d : Nat) (o : NatOption) : Nat :=
  match o with
  | .some n' => n'
  | .none => d

-- Exercise: hd_error (2 stars)
def hd_error (l : NatList) : NatOption := sorry

-- Exercise: option_elim_hd (1 star)
theorem option_elim_hd (l : NatList) (default : Nat) : hd default l = option_elim default (hd_error l) := by sorry

end NatList

-- =================================================================
-- Partial Maps
-- =================================================================

inductive Id : Type where
  | id (n : Nat)

def eqb_id (x1 x2 : Id) : Bool :=
  match x1, x2 with
  | .id n1, .id n2 => n1 == n2

-- Exercise: eqb_id_refl (1 star)
theorem eqb_id_refl (x : Id) : eqb_id x x = true := by sorry

namespace PartialMap
-- Note: NatList definitions are open above.
open NatList

inductive PartialMap : Type where
  | empty
  | record (i : Id) (v : Nat) (m : PartialMap)

def update (d : PartialMap) (x : Id) (value : Nat) : PartialMap :=
  .record x value d

def find (x : Id) (d : PartialMap) : NatOption :=
  match d with
  | .empty => .none
  | .record y v d' =>
    if eqb_id x y = true then .some v
    else find x d'

-- Exercise: update_eq (1 star)
theorem update_eq (d : PartialMap) (x : Id) (v : Nat) : find x (update d x v) = .some v := by sorry

-- Exercise: update_neq (1 star)
theorem update_neq (d : PartialMap) (x y : Id) (o : Nat) (H : eqb_id x y = false) : find x (update d y o) = find x d := by sorry

end PartialMap
end LF
