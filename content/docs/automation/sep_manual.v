(*|
SkyLabs Core Automation
=======================

This package implements a general-purpose, efficient and extensible automation
tactic for the [Iris separation logic](https://iris-project.org) called `sep`.

### Known issues

* Loading this library force-disables Rocq backtraces, because of
  https://github.com/ocaml/dune/issues/10560.
  To re-enable backtraces after loading, use  `Set Debug "backtrace"`.

Automation Setup
----------------

The `sep` tactic requires a bit of setup before it can be used. In particular,
a hint database needs to be created to hold various internal configurations as
well as user-defined extensions (e.g., hints).

The following snippet is an example setup for using the automation. It is also
found in file [automation.v](./examples/tutorial/automation.v).
|*)
(* Export the SkyLabs automation. *)
Require Export skylabs.auto.core.sep.

(* Create a main hint database, to which we add internal automation config. *)
#[global] Create HintDb main discriminated.
Copy HintDb config_db Into main.

(* Enable identidy cancellation in [main]. *)
#[global] Hint Resolve ID_CANCEL | 95 : main.

(* Define user-facing [work] tactic based on [sep], and using [main]. *)
Tactic Notation "work" sl_modifier_list(ms) := sep with main* ${ms}.
(*|
A database called `main` is created, and extended with the automation-internal
configuration. It is also extended with hint `ID_CANCEL`, which specifies that
identity cancellation is enabled in `main`. Finally, tactic notation `work` is
defined as an extension of `sep`, with `main` being setup as "main" database.

The `work` tactic can then be used to solve separation logic goals such as the
following (found in file [t01_basic.v](./examples/tutorial/t01_basic.v)).
|*)
Require Import iris.bi.bi.
Require Import skylabs_auto_core.examples.tutorial.automation.

Section with_prop.
  Context (PROP : bi).
  Context (A B C : PROP).

  Goal B ∗ □ A ∗ C ∗ emp ⊢ emp ∗ A ∗ B ∗ emp ∗ A ∗ C.
  Proof. work. Qed.
End with_prop.

(*|
Extension With User-Defined Hints
---------------------------------

The following example, from file [t02_hint.v](./examples/tutorial/t02_hint.v),
demonstrates how one can register hints in the `main` database. The hint named
`hint_BC_D` is defined from the axiom `BC_D` using notation `[CANCEL] BC_D`. A
later section will go into more details as to how this works.
|*)
Require Import iris.bi.bi.
Require Import iris.proofmode.proofmode.
Require Import skylabs_auto_core.examples.tutorial.automation.
Require Import skylabs.auto.core.hints.

Section with_prop.
  Context (PROP : bi).
  Context (A B C D : PROP).
  Context (BC_D : B ∗ C ⊢ D).

  (* Manually apply [BC_D]. *)
  Goal B ∗ □ A ∗ C ∗ emp ⊢ emp ∗ A ∗ D ∗ emp ∗ A.
  Proof using BC_D. work. iApply BC_D. work. Qed.

  (* Add [BC_D] to the [main] database as a cancellation hint. *)
  Definition hint_BC_D := [CANCEL] BC_D.
  Hint Resolve hint_BC_D : main.

  Goal B ∗ □ A ∗ C ∗ emp ⊢ emp ∗ A ∗ D ∗ emp ∗ A.
  Proof using BC_D. work. Qed.
End with_prop.
(*|

  Automation Tactical Interface
  -----------------------------

In this section, we describe the interface of the `sep` tactic, i.e., the Ltac
entry point of the automation. The `sep` tactic is configured by appending any
number of "modifiers" to the `sep` identifier. For example:
```coq
sep with db* typeclass_instances using H /=.
```
invokes the automation with three modifiers:
- `with db* typeclass_instances` specifies hint databases,
- `using H` specifies a single hint,
- `/=` enables simplification (see below)

### `with db1 ... dbN` modifier

The `with` modifier extends the set of hint databases in which the tactic will
look for user-defined hints. At least one database identifier should be passed
as argument, and each such identifier can optionally be prefixed with flags.

The following flags are available:
- A fuel limit flag (syntax `{i}`) limiting the number of hints that can be
  applied from the database to the given number (`i`).
- A usage requirement flag (syntax `{!i}`) conditioning the success of the
  tactic to at least the given number (`i`) of hints from the database having
  been applied.
- A must-use flag (syntax `!`) with the same effect as `{!1}`.
- A syntactic matching flag (syntax `#`) indicating that the automation will
  match the hints from the database only syntactically.

Additionally, one database per invocation of `sep` must be marked as principal
by adding a `*` suffix to its identifier. The principal database is special in
two ways: (1) it must contain automation-internal configurations, and (2), its
hint opacity configuration is used by the automation.

### `using t1, ..., tN` modifier

The `using` modifier can be used to register individual hints to be used by
the automation. It can take any number of comma-separated terms as argument,
and these can optionally be prefixed by flags.

The following flags are available:
- A fuel limit flag (syntax `{i}`, see above).
- A usage requirement flag (syntax `{!i}`, see above).
- A must-use flag (syntax `!`) with the same effect as `{!1}`.
- A syntactic matching flag (syntax `#`, see above).

### `$key=value` flag modifier

Flag modifiers associate values to flag keys (i.e., identifiers). Valid values
are booleans (`true` or `false`), integers, strings, optional value (using the
`none` or `some(value)` constructors), or pairs of values `(value1, value2)`.

Currently supported options are:
- `simplify` (boolean): indicates whether simplification is enabled.
  This instructs the automation to run `simpl` on the goal when it can
  no longer make progress by other means. (`simpl` ignores `simpl never`
  annotations in some cases and is thus dangerous to run.)
- `evars` (string option): indicates what kind of evar (if any) should be used
  to destruct existentials. The value `none` means that no evars are used,
  `some("normal")` leads to standard evars being used, and `some("protected")`
  leads to protected evars being used.
- `usenamed` (boolean): indicates whether named IPM variables should be used.

Note that the special syntax `/=` is equivalent to `$simplify=true`.

### `${m}` extension modifier

The syntax `${m}` can be used to embed a (list of) modifiers parsed as the
arguments of a tactic notation. Such arguments are produced using a custom
non-terminal `sl_modifier` (similar to `ident` or `constr` for example). It
can be combined with list combinators (e.g., with `sl_modifier_list`).

As an example, one can define an extension of `sep` using
```
Tactic Notation "mysep" sl_modifier_list(ms) :=
  sep with my_db* using my_hint ${ms}.
```
and the resulting tactic will itself support arbitrary modifiers.

Defining Hints
--------------

User-defined hints are defined as instances of special hint classes. Hints can
be registered into hint databases (passed to `sep` using the `with` modifier),
or passed to `sep` with the `using` modifier, as explained above.

### Hint classes

It is **discouraged to define hint instances directly** since hint classes are
subject to changes and extensions (they are an implementation detail).

#### Forward hint (`Fwd`)

See [fwd.v](theories/hints/classes/fwd.v).

#### Backward hint (`Bwd`)

See [bwd.v](theories/hints/classes/bwd.v).

#### Extended cancellation hint (`CancelX`)

See [cancelx.v](theories/hints/classes/cancelx.v).

#### Learning hints

TODO

### Hint DSL

The hint DSL is **the preferred way** to declare hints.

See [cancelx_notation.v](theories/hints/cancelx_notation.v).

### Deriving hints from lemmas

See [orient.v](theories/hints/orient.v).


|*)
