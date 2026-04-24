---
title: wapply
key: skylabs.auto.tactics.wapply
---
(*| `wapply lem`

    Applies lemma `lem` using "footprint inference".

    Requires:
    - `lem : forall x .., ... -> P ⊢ Q -∗ R`
    In goal: `Prems ⊢ Concl`
    Reduces to:
    - `Prems ⊢ P ∗ Q ∗ (R -∗ Concl)`

    `wapply` supports idiomatic IPM lemma structure which prefers
    `P ⊢ Q -∗ R` to (the equivalent) `P ∗ Q ⊢ R`.

    Typeclass side-conditions that arise when applying `lem` are solved
    immediately while non-typeclass side-conditions are left as side-conditions,
    i.e. they are introduced *after* the main goal. Idiomatically, these
    side conditions are often solved using
    - ssreflect notation: e.g. `=> //`, or
    - Ltac chaining, e.g. `; [ | .. done ]`, or
    - explicitly using focusing, e.g. `2:{ ... }`.

    Compared to `iDestruct`, `wapply` allows applying a lemma
    without satisfying its premises immediately.
    For example, suppose that you have premises `_ : V , _ : X ∗ Y` and you
    want to apply a lemma of the form `lem : X ∗ V ⊢ K`. Rather than splitting
    the second premise and manually satisfying the premises of `lem`, you can
    use `wapply lem` to move the premise obligations into the goal which
    leads to a more goal-directed proof which is amenable to powerful
    automation such as `work`.
 |*)
