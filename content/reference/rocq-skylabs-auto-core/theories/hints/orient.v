---
title: Syntax for defining hints
key: bluerock.auto.core.hints.orient
---
(*|
This module defines notations that can convert certain BI facts into hints
for the automation. To this end it offers several notations that can parse
various BI (bi-)entailments into forward, backward, and cancellation hints.

## Simple Examples

### Forward hints
Given a proof `H : P |-- Q`, we use the notation `[FWD] H` to obtain a forward
hint `Fwd P`, which exchanges premise `P` for premise `Q`.
```coq
Lemma hintPQ : P |-- Q.
Proof. (* proof of the hint *) Qed.
Definition hintPQ_F (* : Fwd P *) := [FWD] hintPQ.
```
As a convention, we use the suffix `_F` for forward hints, `_B` for backward hints,
and `_C` for cancellation hints.

### Backwards hint
Given a proof `H : P |-- Q` we use the notation `[BWD] H` to obtain a
backward hint `Bwd Q`, which exchanges conclusion `Q` for conclusion `P`.
```coq
Definition hintPQ_B (* : Bwd P *) := [BWD] hintPQ.
```

### Cancellation hints
Given a proof `H : P |-- P' ** (Q' -∗ Q)`, we use the notation `[CANCEL] H` to
obtain a cancellation hint `Cancel P Q` that exchanges premise `P` for
premise `P'`, and conclusion `Q` for conclusion `Q'`.
```coq
Lemma hintPQ' : P |-- P' ** (Q' -∗ Q).
Proof. (* proof of the hint *) Qed.
Definition hintPQ'_C (* : Cancel P Q *) := [CANCEL] hintPQ'.
```

## Advanced Features
- The notations can parse (bi-)entailments that introduce new facts into the
  Rocq context. For example, `H : P |- ∃ (x : Z) (Hx : 1 <= x), Q x` is
  turned into a forward hint `Fwd P` that introduces `(x : Z)` and
  `(Hx : 1 <= x)` into the Rocq context and exchanges `P` for `Q x` via `[FWD] H`.
- The notations can also parse existential binders in the conclusion. These
  existentials are hoisted to the very top-level of the conclusion. For
  example, `[CANCEL] H` turns `H : P |- (∃ x : Z, Q' x) -∗ Q` into a cancellation
  hint `Cancel P Q` such that it transforms the goal `P |- R ** Q` into
  `P |- ∃ x : Z, R ** Q' x`.

## Re-Orienting Hints
All notations in this module also optionally re-orient bi-entailments.
Given `H : P -|- Q`, we can derive `Fwd Q` (instead of `Fwd P`) via
`[FWD<-] H`. (Note the backward arrow.)

## Specification
The full set of notations is:
- `[FWD]`, `[BWD]`, `[CANCEL]`
- or, equivalently, `[FWD->]`, `[BWD<-]`, `[CANCEL->]` (note the backward
  arrow on `[BWD]`, which indicates the default direction of a backward hint)
- or, to reverse bi-entailments, `[FWD<-]`, `[BWD->]`, `[CANCEL<-]`.

The general form of hints parsed by the notations is:
- `P |-- ∃ x1 .. xN, P' ** ((∃ y1 .. yM, Q') -* Q)`
  where `P'` can mention `x1 .. xN`, `Q'` can mention `x1 .. xN` and `y1 ..
  yM`, and `P` and `Q` may not mention either set of binders.

The tactics will parse lemmas whose type ends in one of the above forms by
introducing universal quantifiers and implications it encounters while
traversing the type and mirroring them in the resulting hint.
|*)
