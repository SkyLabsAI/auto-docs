---
title: Derive `Bwd` hints
key: bluerock.auto.elpi.derive.bwd
---
(*|
:::warn
This command does not yet support usages inside `Section`s.
:::
Usage: `#[only(DIR)] derive Lem.` where `Lem` is an equivalence
`forall ..., LHS ... -|- RHS ...` or an entailment `forall ..., LHS
... |-- RHS ...` registers an `export`ed `Bwd` hint based on
`Lem`:

- if `DIR` is `bwd` or `bwd(r2l)`: replace RHS by LHS (corresponds to `[BWD<-]`)

- if `DIR = bwd(l2r)`: replace LHS by RHS (corresponds to `[BWD->]`, ONLY
for `Lem` being an equivalence)


For example, with
```coq
Lemma lemPQ : P |-- Q.
Proof. (* proof of the hint *) Qed.
```
```coq
#[only(bwd)] derive lemPQ.
```
is similar to
```coq
Definition lemPQ_B (* : Bwd P *) := [BWD] lemPQ.
```
|*)
