---
title: Derive instances for BI predicates
key: bluerock.auto.cpp.elpi.derive.bi
---
(*|
The command `derive` supports generating, mainly for `Rep` and `mpred`, `#[global]` instances of:
- `Knowledge`
- `Timeless`
- `ExclusiveToken0`
- `Typed cls _`/ `Observe (type_ptrR (Tnamed cls)) _`
- `Fractional`, `FracValid0`, `AsFractional0`
- `CFractional`, `CFracValid0`, `AsCFractional0`
- `WeaklyObjective`

`cfracsplittable` derivation generates instances of `Timeless`, `CFractional`,
`AsCFractional0` and `CFracValid0`, and *not* `CFracSplittable_0`.
This is also the same for `fracsplittable`.

Locked predicates using `mlock` and `br.lock` are supported as well as `Parameter`s.

For definitions, the command tries to solve `Knowledge` by `solve_knowledge`,
`Timeless` and `Typed` by `solve_TC`
(the C++ type in `Typed` is an evar that should be solved by typeclass search);
and `ExclusiveToken0` by `solve_exclusive`.

The instances can be referred to by the convention `[Pred]_[instance type]`, e.g. `R_timeless`.

## Usages:
```coq
#[only(knowledge)] derive Pred.
#[only(timeless)] derive Pred.
#[only(exclusive)] derive Pred.
#[only(type_ptr)] derive Pred.
#[only(timeless,knowledge)] derive Pred.
#[only(cfractional,cfracvalid,ascfractional)] derive Pred.
#[only(cfracsplittable)] derive Pred.
#[only(fractional,fracvalid,asfractional)] derive Pred.
#[only(fracsplittable)] derive Pred.
#[only(wobjective)] derive Pred.
```

## Examples:
```coq
br.lock
Definition prim0R `{Σ : cpp_logic} {σ : genv} (q : cQp.t) : Rep := primR Tint q 0.
#[only(timeless)] derive prim0R.
```
This generates the following instance:
```coq
#[global] Instance prim0R_timeless : ∀ ti _Σ Σ σ q, Timeless (@prim0R ti _Σ Σ σ q).
Proof. rewrite prim0R.unlock. apply _. Qed.
```

Meanwhile
```coq
Parameter R : ∀ `{Σ : !cpp_logic ti _Σ} (q : cQp.t), mpred.
#[only(timeless)] derive R.
```
declares the following instance, because `R` is a `Parameter`.
```coq
#[global] Declare Instance R_timeless : ∀ ti _Σ Σ q, Timeless (@R ti _Σ Σ q).
```
|*)
