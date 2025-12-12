---
title: Derive `Hint Opaque` annotations
key: bluerock.auto.elpi.derive.hint_opaque
---
(*|
Usage: `#[only(hint_opaque)] derive R.` to mark `R` opaque (globally) in the database `br_opacity`.

This is similar to
```coq
#[global] Hint Opaque R : br_opacity.
```
|*)
