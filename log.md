# Lemma vs Theorem in Lean4
## Why it happened
In Lean 4 without Mathlib imported, `lemma` is not a keyword (unlike `theorem`). Since `lemma` is not recognized as a command keyword, Lean treated `lemma` as an ordinary identifier.

As a result, Lean tried to parse `lemma` as a continuation of the previous line. It looked at the expression ... → x = y from the def injective line and thought you were trying to apply the result of x = y as a function to the argument lemma (essentially as if you wrote (x = y) lemma). Since the expression x = y evaluates to a Prop (which has type A in this context depending on how the typechecker interprets the error state), it threw the error: "Expected a function because this term is being applied to the argument lemma".

## How I fixed it
I replaced `lemma succ_inj` with `theorem succ_inj` on line 20 in lf/Logic.lean. 
Now Lean 4 recognizes theorem as a command, correctly terminating the previous def statement, and the file compiles successfully!