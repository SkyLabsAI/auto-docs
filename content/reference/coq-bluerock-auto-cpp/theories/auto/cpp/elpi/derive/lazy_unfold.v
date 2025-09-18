---
title: Derive Lazy unfolding hints
key: bluerock.auto.elpi.derive.lazy_unfold
---
(*|
:::warn
This command does not yet support usages inside `Section`s.
:::
## Usages
- `#[only(lazy_unfold(locality)] derive R.` where `locality ∈ { global, local, export }`
- `#[only(lazy_unfold)] derive R.` is the same as `#[only(lazy_unfold(export))] R.`

The command defines and registers lazy unfolding hints for `R`.

For example,
```coq
Definition R `{Σ : cpp_logic} {σ : genv} (q : cQp.t) : Rep := Rbody q.
#[only(lazy_unfold)] derive R.
```
registers a (`export`ed) hint of the form `∀ q, R q -|- Rbody q`
that will only trigger when the goal contains `Rbody q`.
|*)
