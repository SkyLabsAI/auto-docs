---
title: "The anatomy of an Iris goal"
tags:
- learn
- iris
requires: []
provides:
- iris_goals
eleventyNavigation:
  order: 202
  parent: learn
---

Both the IPM tactics and the `sep` family of tactics work on Iris goals such as the following:

```rocq
n, m : Z
H : n + 1 = m
--------------------------------------
"HP2" : P2
_ : P1
--------------------------------------□
"HQ1" : Q1
_ : Q2
--------------------------------------∗
R
```

Here, we must prove `R` assuming `P1`, `P2`, `Q1` and `Q2`.
Assumption `P1` and `P2` can be duplicated or discarded
freely, unlike `Q1` and `Q2`: We say `P1` and `P2` are intuitionistic and form
the intuitionistic context, while `Q1` and `Q2` form the spatial context.

Iris assumptions can be named or anonymous. Tactics can use names to act on
specific hypotheses, but otherwise names are not meaningful.

Sometimes, we might refer to these goals as `Γ ; Γp ; Γs ⊢ Q`, where `Γ` is the
Rocq context, `Γp` is the intuitionistic context, `Γs` is the spatial context,
and `Q` is the conclusion.

A plain Iris entailment `P ⊢ Q` can be converted via `iStartProof` to the following Iris goal

```rocq
--------------------------------------∗
P -∗ Q
```
