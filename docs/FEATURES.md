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
## Features
- [x] **F1:** Translate Basics
    - [x] **T1.1:** Translate Data and Functions (Enumerated Types, Days, Booleans, Types, Modules, Tuples, Numbers)
    - [x] **T1.2:** Translate Proof by Simplification and Proof by Rewriting
    - [x] **T1.3:** Translate Proof by Case Analysis
    - [x] **T1.4:** Translate More Exercises, but keep them empty
- [ ] **F2:** Translate Induction
- [ ] **F3:** Translate Lists
- [ ] **F4:** Translate Poly
- [ ] **F5:** Translate Tactics
- [ ] **F6:** Translate Logic
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
- [ ] **F18:** Translate Postscript
- [ ] **F19:** Translate Bib