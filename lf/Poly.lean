import lf.Lists

namespace LF
namespace Poly

-- =================================================================
-- Polymorphism
-- =================================================================

inductive List (X : Type) : Type where
  | nil : List X
  | cons (x : X) (l : List X) : List X

def repeat_func {X : Type} (x : X) (count : Nat) : List X :=
  match count with
  | 0 => .nil
  | count' + 1 => .cons x (repeat_func x count')

def app {X : Type} (l1 l2 : List X) : List X :=
  match l1 with
  | .nil => l2
  | .cons h t => .cons h (app t l2)

def rev {X : Type} (l : List X) : List X :=
  match l with
  | .nil => .nil
  | .cons h t => app (rev t) (.cons h .nil)

def length {X : Type} (l : List X) : Nat :=
  match l with
  | .nil => 0
  | .cons _ l' => length l' + 1

local notation " [] " => List.nil
local notation "[" "]" => List.nil
local infixr:60 " :: " => List.cons
local infixr:60 " ++ " => app

-- Exercise: poly_exercises (2 stars)
theorem app_nil_r {X : Type} (l : List X) : l ++ [] = l := by sorry

theorem app_assoc {X : Type} (l m n : List X) : l ++ m ++ n = (l ++ m) ++ n := by sorry

theorem app_length {X : Type} (l1 l2 : List X) : length (l1 ++ l2) = length l1 + length l2 := by sorry

-- Exercise: more_poly_exercises (2 stars)
theorem rev_app_distr {X : Type} (l1 l2 : List X) : rev (l1 ++ l2) = rev l2 ++ rev l1 := by sorry

theorem rev_involutive {X : Type} (l : List X) : rev (rev l) = l := by sorry

-- =================================================================
-- Polymorphic Pairs
-- =================================================================

inductive Prod (X Y : Type) : Type where
  | pair (x : X) (y : Y)

def fst {X Y : Type} (p : Prod X Y) : X :=
  match p with
  | .pair x _ => x

def snd {X Y : Type} (p : Prod X Y) : Y :=
  match p with
  | .pair _ y => y

def combine {X Y : Type} (lx : List X) (ly : List Y) : List (Prod X Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => Prod.pair x y :: combine tx ty

-- Exercise: split (2 stars)
def split {X Y : Type} (l : List (Prod X Y)) : Prod (List X) (List Y) := sorry

-- =================================================================
-- Polymorphic Options
-- =================================================================

inductive Option (X : Type) : Type where
  | some (x : X)
  | none

def nth_error {X : Type} (l : List X) (n : Nat) : Option X :=
  match l with
  | [] => .none
  | a :: l' =>
    match n with
    | 0 => .some a
    | n' + 1 => nth_error l' n'

-- Exercise: hd_error_poly (1 star)
def hd_error {X : Type} (l : List X) : Option X := sorry

-- =================================================================
-- Functions as Data
-- =================================================================

def doit3times {X : Type} (f : X → X) (n : X) : X :=
  f (f (f n))

def filter {X : Type} (test : X → Bool) (l : List X) : List X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: filter test t
    else filter test t

def length_is_1 {X : Type} (l : List X) : Bool :=
  length l == 1

def countoddmembers' (l : List Nat) : Nat :=
  length (filter LF.odd l)

-- Exercise: filter_even_gt7 (2 stars)
def filter_even_gt7 (l : List Nat) : List Nat := sorry

-- Exercise: partition (3 stars)
def partition {X : Type} (test : X → Bool) (l : List X) : Prod (List X) (List X) := sorry

def map {X Y : Type} (f : X → Y) (l : List X) : List Y :=
  match l with
  | [] => []
  | h :: t => f h :: map f t

-- Exercise: map_rev (3 stars)
theorem map_rev {X Y : Type} (f : X → Y) (l : List X) : map f (rev l) = rev (map f l) := by sorry

-- Exercise: flat_map (2 stars)
def flat_map {X Y : Type} (f : X → List Y) (l : List X) : List Y := sorry

def option_map {X Y : Type} (f : X → Y) (xo : Option X) : Option Y :=
  match xo with
  | .none => .none
  | .some x => .some (f x)

-- =================================================================
-- Fold
-- =================================================================

def fold {X Y : Type} (f : X → Y → Y) (l : List X) (b : Y) : Y :=
  match l with
  | [] => b
  | h :: t => f h (fold f t b)

def constfun {X : Type} (x : X) : Nat → X :=
  fun _ => x

def ftrue := constfun true

def fold_plus := fold Nat.add

-- =================================================================
-- Additional Exercises
-- =================================================================

-- Exercise: fold_length (2 stars)
def fold_length {X : Type} (l : List X) : Nat :=
  fold (fun _ n => n + 1) l 0

theorem fold_length_correct {X : Type} (l : List X) : fold_length l = length l := by sorry

-- Exercise: fold_map (3 stars)
def fold_map {X Y : Type} (f : X → Y) (l : List X) : List Y := sorry

-- Exercise: currying (2 stars)
def prod_curry {X Y Z : Type} (f : Prod X Y → Z) (x : X) (y : Y) : Z :=
  f (.pair x y)

def prod_uncurry {X Y Z : Type} (f : X → Y → Z) (p : Prod X Y) : Z := sorry

theorem uncurry_curry {X Y Z : Type} (f : X → Y → Z) (x : X) (y : Y) : prod_curry (prod_uncurry f) x y = f x y := by sorry

theorem curry_uncurry {X Y Z : Type} (f : Prod X Y → Z) (p : Prod X Y) : prod_uncurry (prod_curry f) p = f p := by sorry

-- =================================================================
-- Church Numerals (Advanced)
-- =================================================================

namespace Church

def cnat := ∀ X : Type, (X → X) → X → X

def one : cnat :=
  fun _ f x => f x

def two : cnat :=
  fun _ f x => f (f x)

def zero : cnat :=
  fun _ _ x => x

def three : cnat := @doit3times
-- Wait, doit3times relies on implicit arguments and requires implicit variables properly instantiated.
-- Coq had: Definition three : cnat := @doit3times.
-- In Lean, it might complain about implicit arguments not matching.
-- Let me wrap it inside an explicit fun:
-- def three : cnat := fun X f x => doit3times f x

-- Let me test @doit3times first...Actually let's just use the lambda to avoid implicit argument mismatch issues. Lean treats universe levels differently and `@doit3times` might not cleanly cast to `cnat`.
-- Lean 4 has problems if universes aren't explicitly unified, `cnat` works on `Type`.
-- So I'll write:
-- def three : cnat := fun X f x => doit3times (X := X) f x

-- Exercise: church_scc (2 stars)
def scc (n : cnat) : cnat := sorry

-- Exercise: church_plus (3 stars)
def plus (n m : cnat) : cnat := sorry

-- Exercise: church_mult (3 stars)
def mult (n m : cnat) : cnat := sorry

-- Exercise: church_exp (3 stars)
def exp (n m : cnat) : cnat := sorry

end Church
end Poly
end LF
