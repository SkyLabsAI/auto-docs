---
title: Derive instances for BI predicates
---
(*|
This supports generating, mainly for `Rep` and `mpred`, `#[global]` instances of:
- `Knowledge`
- `Timeless`
- `ExclusiveToken0`
- `Typed cls _`/ `Observe (type_ptrR (Tanemd cls)) _`
- `Fractional`, `FracValid0`, `AsFractional0`
- `CFractional`, `CFracValid0`, `AsCFractional0`
- `WeaklyObjective`

`cfracsplittable` derivation generates instances of `Timeless`, `CFractional`,
`AsCFractional0` and `CFracValid0`, and *not* `CFracSplittable_0`.
This is also the same for `fracsplittable`.

Locked predicates using `mlock` and `br.lock` are supported as well as `Parameter`s.

## Usages:
```coq
#[only(knowledge)] derive Pred.
#[only(timeless)] derive Pred.
#[only(exclusive)] derive Pred.
#[only(type_ptr)] derive Pred.
#[only(timeless,knowledge)] derive Pred.
#[only(cfracsplittable)] derive Pred.
#[only(fracsplittable)] derive Pred.
#[only(wobjective)] derive Pred.
```

## Example generation:
```coq
Pred_knowledge : ∀ `(Σ : cpp_logic) (x1 : A1) ⋯ (xn : AN), Knowledge (Pred x1 ⋯ xn).
```

`Knowledge` is solved by `solve_knowledge`,
`Timeless` and `Typed` is solved by `solve_TC`
(the C++ type in `Typed` is an evar that should be solved by typeclass search).
`ExclusiveToken0` is solved by `solve_exclusive`.
|*)
