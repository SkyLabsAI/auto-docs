---
title: Derive equivalences for predicates
key: bluerock.auto.elpi.derive.equiv
provides:
- derive
- equiv
---
(*|
Usages: `#[only(equiv)] derive R.`

For example,
```coq
Definition R `{Σ : cpp_logic} {σ : genv} q : Rep := Rbody q.
#[only(equiv)] derive R.
```
proves the lemma `R_equiv : ∀ q, R q -|- Rbody q`.
|*)
