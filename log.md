# Lemma vs Theorem in Lean4
## Why it happened
In Lean 4 without Mathlib imported, `lemma` is not a keyword (unlike `theorem`). Since `lemma` is not recognized as a command keyword, Lean treated `lemma` as an ordinary identifier.

As a result, Lean tried to parse `lemma` as a continuation of the previous line. It looked at the expression ... → x = y from the def injective line and thought you were trying to apply the result of x = y as a function to the argument lemma (essentially as if you wrote (x = y) lemma). Since the expression x = y evaluates to a Prop (which has type A in this context depending on how the typechecker interprets the error state), it threw the error: "Expected a function because this term is being applied to the argument lemma".

## How I fixed it
I replaced `lemma succ_inj` with `theorem succ_inj` on line 20 in lf/Logic.lean. 

# The fixes included:
   1. Ensuring the full resolution of the Collatz_holds_for 12 example by manually laying out the complete proof instead of using repeat.
   2. Resolving ambiguity issues with ≤ by declaring an explicit namespace/prefix when needed, specifically replacing generic variables with typed ones (e.g., (3 : Nat) ≤ (5
      : Nat)) to guide inference correctly.
   3. Modifying evSS_ev to utilize Lean 4's injection properly by chaining injections and correctly tracking explicit variables in goals.
   4. Correcting the proof structure of ev_Even using omega to easily solve the equation mapping after the correct instantiation of cases.
   5. Explicitly binding implicit variables and explicit types (like (n m : Nat)) for theorems referring to # and inequalities.

# Bug
IndProp.lean
- Induction on Evidence