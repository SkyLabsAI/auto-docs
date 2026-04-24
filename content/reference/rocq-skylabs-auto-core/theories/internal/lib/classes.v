---
title: RedEq
key: skylabs.auto.internal.lib.classes.red_eq
---
(*|
# `RedEq`

`RedEq` can be used in place of premises of the shape [a = b] which are
supposed to be resolved automatically via in typeclass search with the help
of `vm_compute`, `whd`, `cbv`, `lazy`, `cbn`, `simpl`.

It's `Side` argument is one of `Left`, `Right`, `Both`, indicating which
side(s) are to be reduced before solving the goal via unification.

All users are expected to use the provided notations:
- `a =[Vm]=> b` for `RedEq RedVm Left ClosedTerms a b`,
  useful in particular for `f x =[Vm]=> Some y`
- `a <=[Vm]= b` for `RedEq RedVm Right ClosedTerms a b`
- `a  =[Vm]= b` for `RedEq RedVm Both ClosedTerms a b`.
(And similarly for other reduction strategies.)

By default, only closed terms are reduced (`ClosedTerms`). But this
restriction can be lifted by adding a <<+>> or <<?>> to the reduction:
- `=[Vm+]=>` allows open terms but not evars
- `=[Vm?]=>` allows all terms
|*)
Inductive Side :=
| Left
| Both.

Inductive TermRestriction :=
| ClosedTerms                   (* Free of axioms and evars. *)
| EvarFreeTerms                 (* Free of evars *)
| AllTerms.                     (* Any terms *)

Inductive ReductionStrategy :=
| RedVm
| RedWhd
| RedLazy
| RedLazyBeta
| RedCbn
| RedCbv
| RedSimpl.
