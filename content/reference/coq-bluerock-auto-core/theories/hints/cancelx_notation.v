---
title: DSL for `CancelX` hints
---
(*|
This file defines a DSL to simplify to definition and proof of hints. The same language is usable with [Bwd], [Fwd]
and [CancelX] hints. Fwd hints are still special since they're run at a different phase.
## [CancelX] Hints
The following defines a [CancelX] hint:
```coq
#[program]
Definition my_cancelx_C :=
  \cancelx
  \masks m => f       (* [m : MatchingMode] and [f : FUpdCfg]; see classes/cancelx.v *)
  \with a
  \guard isGood a     (* this is like \require *)
  \guard_with b       (* inserts [guard_not_provable (guard_with b)] and introduces [guard_with b] *)
  \with b
  \using P a b          (* match and _use_ [P a b]; see [base.Use] documentation *)
  \consuming P' a b     (* match and always consume [P a b]; see [base.Drop] documentation *)
  \preserving PP a b    (* match and always preserve [PP a b]; like \prepost PP; see [base.Preserve] documentation *)
  \intro c              (* c is only visible in \deduce and \through *)
  \deduce P' a b c
  \bound x              (* x is only visible in \proving, \through and \frame *)
  \bound_guard good_instance x (* like \bound but meant for discriminating between matches *)
  \proving Q a b x      (* final goal to match *)
  \goal_trigger QQ a b x
  \whole_conclusion     (* only fire if the hint matches all conjuncts of the conclusion *)
  \exist y              (* y is only visible in \through *)
  \through Q' a b c x y   (* new goal *)
  \frame L a b x        (* bi-abduction frame; once Q' ** QQ are dischared, L can become a new assumption *)
  \end.
Next Obligation. (* Proof of the hint *) Qed.
```
The resulting hint statement is equivalent to:
```coq
forall a, isGood a ->
forall b,
  P a b ** PP a b
|-- exists c,
      P' a b c ** PP a b **
      (forall x (_ : good_instance x),
          (exists y, Q' a b c x y ** QQ a b x) -*
      Q a b x ** QQ a b x ** L a b x)
```
Note that the variables' visibility follow the rules indicated in comments and not the visitibilty rules of the
quantifiers in the above formula. Case in point, even though [Q] and [QQ] appear under [exists c] (the intro-ed variable),
they cannot refer to [c].
## [Bwd] Hints
The following defines a [Bwd] hint:
```coq
#[program]
  Definition my_bwd_hint_C :=
    \bwd
    \with a
    \bound b   (* in a bwd hint, \bound is the same as \with *)
    \proving Q a b
    \goal_trigger QQ a b
    \intro c
    \through Q' a b c
    \end .
Next Obligation. (* Proof of the hint *) Qed.
```
The resulting hint statement is equivalent to:
```coq
forall a b, (exists c, Q' a b c ** QQ a b) |-- Q a b ** QQ a b
```
# [Fwd] Hints
The following defines a [Fwd] hint:
```coq
#[program]
  Definition my_fwd_hint_C :=
    \fwd
    \with a
    \consuming P a
    \using PP a
    \intro b
    \deduce P' a b
    \end .
Next Obligation. (* Proof of the hint *) Qed.
```
The resulting hint statement is equivalent to:
```coq
  forall a, P a ** PP a |-- exists b, P' a b ** PP a
```
## Binders
Each keyword that declares a predicate can additionally bind one or more variable with an appropriate binder. Here is
how to desugar those variable declarations:
```coq
    \guard{a} isGood a
  ~>
    \with a
    \guard isGood a
    \consuming{a} P a

  ~>
    \with a
    \consuming P a
    \using{a} PP a

  ~>
    \with a
    \using PP a
    \deduce{b} P' b

  ~>
    \intro b
    \deduce P' b
    \proving{x} Q x

  ~>
    \bound x
    \proving Q x
    \goal_trigger{x} QQ x

  ~>
    \bound x
    \goal_trigger QQ x
    \through{y} Q' y

  ~>
    \exist y
    \through Q' y
    \frame{a} P a

  ~>
    \bound a
    \frame P a
```
|*)
