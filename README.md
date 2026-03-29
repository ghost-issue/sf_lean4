# Syntax

> Lean4: No `.` and `end.` and `Qed.`

## Lean4 and Coq (Same)
- exact
- apply
- intros
- assumption
- unfold
- contradiction
- constructor
- induction
- repeat
- try
- refine
- specialize
- clear
- trivial

## Lean4 vs. Coq

| Feature | Lean 4 | Coq |
| :--- | :--- | :--- |
| **Inductive Type** | `inductive T : Type where` | `Inductive t : Type :=` |
| **Definition** | `def name (x : T) : R := ...` | `Definition name (x : T) : R := ...` |
| **Recursive Def** | `def` (terminates automatically) | `Fixpoint` |
| **Pattern Matching** | `match x with \| .alt => ...` | `match x with \| alt => ... end` |
| **Evaluation** | `#eval` | `Compute` |
| **Type Checking** | `#check` | `Check` |
| **Simplification** | `simp` | `simpl` |
| **Reflexivity** | `rfl` | `reflexivity` |
| **Rewrite (Forward)** | `rw [hyp]` | `rewrite hyp` or `rewrite -> hyp` |
| **Rewrite (Backwards)** | `rw [<- hyp]` | `rewrite <- hyp` |
| **Namespace/Module** | `namespace Name ... end Name` | `Module Name. ... End Name.` |
| **Inline Theorem** | `example : Prop := by` | `Example name : Prop. Proof. ... Qed.` |
| **Notation** | `infix:level "sym" => fun` | `Notation "sym" := (fun) (at level n).` |
| **Placeholder/Fail** | `sorry` | `Admitted` (or `Abort` to cancel) |

- [Cheatsheet](Cheat/Cheat.png)

## Reference
- [coq-lean-cheatsheet](https://github.com/funexists/coq-lean-cheatsheet)