# Requirements
This file keeps the Problem statement, features, and tasks of the development project. It is updated on a revolving basis.
Features and tasks have IDs prefixed with F and T, respectively, and are arranged as checklist items. A checked box indicates that the feature or task is done. A feature is checked only of all tasks under it are checked. The following example shows a snapshot:

## Example of Feature checklist
    - [ ] **F1:** Description of feature 1 
        - [x] **T1.1:** the normal case: inner product computed for two vectors of legal and equal dimensions
        - [ ] **T1.2:** exception case: when a vector has an illegal dimension
    - [x] **F2:** Description of a feature 2
        - [x] **T2.1:** Create a `Vector` class that can be constructed and stores vector data.

## Problem statement
goal: translating the whole book to lean4 and keeping exercise empty as same as the original(coq files). 

You can translate follow by toc and make it task by task.

> ps: Don't delete the original!!
> 
> ps: Don't translate the xxxTest.v
>
> ps: Don't traslate the Informal Proofs
## Features
- [x] **F1:** Translate Basics
    - [x] **T1.1:** Translate Data and Functions (Enumerated Types, Days, Booleans, Types, Modules, Tuples, Numbers)
    - [x] **T1.2:** Translate Proof by Simplification and Proof by Rewriting
    - [x] **T1.3:** Translate Proof by Case Analysis
    - [x] **T1.4:** Translate More Exercises, but keep them empty
- [x] **F2:** Translate Induction
    - [x] **T2.1:** Translate Proof by Induction
    - [x] **T2.2:** Translate Proofs Within Proofs
    - [x] **T2.3:** Translate Formal vs. Informal Proof
    - [x] **T2.4:** Translate More Exercises
    - [x] **T2.5:** Translate Nat to Bin and Back to Nat
    - [x] **T2.6:** Translate Bin to Nat and Back to Bin
- [x] **F3:** Translate Lists
    - [x] **T3.1:** Translate Pairs of Numbers
    - [x] **T3.2:** Translate Lists of Numbers
    - [x] **T3.3:** Translate Reasoning About Lists
    - [x] **T3.4:** Translate Search
    - [x] **T3.5:** Translate List Exercises, Part 1
    - [x] **T3.6:** Translate List Exercises, Part 2
    - [x] **T3.7:** Translate Options
    - [x] **T3.8:** Translate Partial Maps
- [x] **F4:** Translate Poly
    - [x] **T4.1:** Translate Polymorphism (Lists, Type Inference, Implicit Args)
    - [x] **T4.2:** Translate Polymorphic Pairs and Options
    - [x] **T4.3:** Translate Functions as Data (Higher-Order, Filter, Map)
    - [x] **T4.4:** Translate Fold and Functions That Construct Functions
    - [x] **T4.5:** Translate Additional Exercises (Church Numerals)
- [x] **F5:** Translate Tactics
    - [x] **T5.1:** Translate The `apply` Tactic and `apply with`
    - [x] **T5.2:** Translate The `injection` and `discriminate` Tactics
    - [x] **T5.3:** Translate Tactics on Hypotheses and Specializing Hypotheses
    - [x] **T5.4:** Translate Varying the Induction Hypothesis
    - [x] **T5.5:** Translate Unfolding Definitions and `destruct` on Compound Expressions
    - [x] **T5.6:** Translate Additional Exercises
- [x] **F6:** Translate Logic
    - [x] **T6.1:** Translate Conjunction and Disjunction
    - [x] **T6.2:** Translate Falsehood, Negation, and Truth
    - [x] **T6.3:** Translate Logical Equivalence and Setoids
    - [x] **T6.4:** Translate Existential Quantification
    - [x] **T6.5:** Translate Functional Extensionality
    - [x] **T6.6:** Translate Classical vs. Constructive Logic
- [ ] **F7:** Translate IndProp
- [ ] **F8:** Translate Maps
- [ ] **F9:** Translate ProofObjects
- [ ] **F10:** Translate IndPrinciples
- [ ] **F11:** Translate Rel
- [ ] **F12:** Translate Imp
- [ ] **F13:** Translate ImpParser
- [ ] **F14:** Translate ImpCEvalFun
- [ ] **F15:** Translate Extraction
- [ ] **F16:** Translate Auto
- [ ] **F17:** Translate AltAuto