---
title: Derive Eager unfolding hints
key: bluerock.auto.elpi.derive.eager_unfold
---
(*|
:::warn
This command does not yet support usages inside `Section`s.
:::

Usages: `#[only(eager_unfold)] derive R.`

The command defines and registers hints that _eagerly_ unfold/unlock predicates.
These hints have locality `export`.

For example
```coq
Definition R `{Σ : cpp_logic} {σ : genv} q : Rep := Rbody q.
#[only(eager_unfold)] derive R.
```
registers a (`export`ed) hint of the form `∀ q, R q -|- Rbody q`
that will only trigger when the goal contains `Rbody q`.
|*)
