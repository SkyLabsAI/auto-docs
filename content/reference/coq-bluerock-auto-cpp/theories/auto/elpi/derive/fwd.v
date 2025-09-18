---
title: Derive `Fwd` hints
key: bluerock.auto.elpi.derive.fwd
---
(*|
:::warn
This command does not yet support usages inside `Section`s.
:::
Usage: `#[only(DIR)] derive Lem.` where `Lem` is an equivalence
`forall ..., LHS ... -|- RHS ...` or an entailment `forall ..., LHS
... |-- RHS ...` registers an `export`ed `Fwd` hint based on
`Lem`:

- if `DIR` is `fwd` or `fwd(l2r)`: replace LHS by RHS (corresponds to `[FWD->]`)

- if `DIR = fwd(l2r)`: replace RHS by LHS (corresponds to `[FWD<-]`, ONLY
for `Lem` an equivalence)

For example, with
```coq
Lemma lemPQ : P |-- Q.
Proof. (* proof of the hint *) Qed.
```
```coq
#[only(fwd)] derive lemPQ.
```
is similar to
```coq
Definition lemPQ_F (* : Fwd P *) := [FWD] lemPQ.
```
|*)
