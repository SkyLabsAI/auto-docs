---
title: Derive `Cancel` hints
key: bluerock.auto.elpi.derive.cancel
---
(*|
:::warn
This command does not yet support usages inside `Section`s.
:::
Usage: `#[only(DIR)] derive Lem.` where `Lem` is an equivalence
`forall ..., LHS ... -|- RHS ...` or an entailment `forall ..., LHS
... |-- RHS ...` registers an `export`ed `Cancel` hint based on
`Lem`:

- if `DIR` is `cancel` or `cancel(l2r)`: cancel RHS with LHS (corresponds to `[CANCEL->]`).
The generated hint has suffix `_l2rC`.


- if `DIR = cancel(l2r)`: cancel LHS by RHS (corresponds to `[CANCEL<-]`, ONLY
for `Lem` an equivalence).
The generated hint has suffix `_r2lC`.

For example, with
```coq
Lemma lemPQ : P |-- Q.
Proof. (* proof of the hint *) Qed.
```
```coq
#[only(cancel)] derive lemPQ.
```
is similar to
```coq
Definition lemPQ_l2rC (* : Cancel P Q *) := [CANCEL] lemPQ.
```
|*)
