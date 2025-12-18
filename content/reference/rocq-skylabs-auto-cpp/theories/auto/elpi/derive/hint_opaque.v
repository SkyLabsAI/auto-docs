---
title: Derive `Hint Opaque` annotations
key: skylabs.auto.elpi.derive.hint_opaque
---
(*|
Usage: `#[only(hint_opaque)] derive R.` to mark `R` opaque (globally) in the database `sl_opacity`.

This is similar to
```coq
#[global] Hint Opaque R : sl_opacity.
```
|*)
