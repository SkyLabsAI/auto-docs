---
title: Common UNSAFE hints for `primR`
key: bluerock.auto.cpp.hints.fractional
---
(*|
This file provides hints that can be registered in order to read primitives which is
*very* common.

:::info
The hints in this file are technically unsafe, but tend to work in practice due
to the way that the weakest pre-condition rules work out.
:::

You should enable one of the hints, but probably not both. Neither is enabled by default.

In cases were you do not need to split your fractions, you can enable.
```coq
  #[local] Hint Resolve UNSAFE_read_prim_cancel : br_opacity.
```
If you do need to split your fractions, you can enable.
```coq
  #[local] Hint Resolve UNSAFE_read_prim_frac_cancel : br_opacity.
```
|*)
