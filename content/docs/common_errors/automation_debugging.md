---
title: "Diagnosing Surprising or Incorrect Proof-State Transitions"
layout: page
eleventyNavigation:
  key: automation-debugging
  title: "Proof-State Transition Diagnosis"
  parent: troubleshooting
  order: 150
---

<p class="small text-body-secondary mb-3">
This guidance assumes you are already comfortable reading BRiCk proof states
and using ordinary Rocq automation, typeclass search, and local proof tools to
rule out simpler explanations before debugging the automation itself.
</p>

This page is for diagnosing proof-state transitions that look surprising,
unhelpful, or outright wrong after running SkyLabs automation.

SkyLabs automation tactics such as `go`, `work`, and `ework` are examples of
the workflow here, but the same diagnosis pattern applies more broadly across
SkyLabs automation.

<h2 id="start-here">Start here</h2>

- [Read the proof state first](#read-the-state-before-the-traces):
  identify the missing proof step before reaching for traces.
- [Follow the diagnosis loop](#core-workflow):
  explain the local state first, then widen to deeper candidate causes only as
  needed.
- [Jump to trace commands when needed](../../../reference/skylabs.auto/):
  use the reference page once the state alone is no longer explanatory.

<h2 id="where-this-fits">Where this fits</h2>

Rocq already provides several automation layers for ordinary proof work:

- [`auto`](https://rocq-prover.org/doc/master/refman/proofs/automatic-tactics/auto.html)
  and related proof search
- [typeclass search and `typeclasses eauto`](https://rocq-prover.org/doc/master/refman/addendum/type-classes.html)
- solver-style tactics such as `lia`, `nia`, and related automation in the
  Rocq ecosystem

SkyLabs automation sits on top of that broader landscape for BRiCk-specific
reasoning about separation logic, weakest preconditions, and proof-state
normalization. It is also user-extensible: custom abstractions and
representations can be connected to the automation with local hints and related
mechanisms. See [Rep hints](../rep_hints/main.v) for one concrete entrypoint.

For built-in Rocq automation debugging, see
[typeclass search and `Set Typeclasses Debug`](https://rocq-prover.org/doc/master/refman/addendum/type-classes.html).
Those tools complement the SkyLabs-specific traces and diagnosis workflow here.

## When to use this

Use this page when:

- automation stops making progress in a way the current goal does not explain
- a tactic call changes the proof state in a surprising or incorrect way
- the resulting goals suggest that useful information was lost or instantiated
  badly
- you need to decide whether the blocker is a missing hint, a blocked side
  condition, the wrong search phase, or a non-automation issue

Do not start here if ordinary automation is still making routine progress. Let
it run until the state becomes informative enough to diagnose.

<h2 id="core-workflow">Core workflow</h2>

1. stop at the first genuinely informative stuck or degraded state
2. state what you expected the next proof step to be, then identify what
   transition actually happened instead
3. inspect traces only once the local state itself is no longer explanatory
4. test the smallest local fix that could confirm or refute the suspected cause
   before widening scope

Sometimes this shows that the issue is not automation at all. The real problem
may be a [proof-strategy issue](./proof_strategy_gotchas.md), a specification
or rep-predicate issue, or a plain bug in the model or code.

<h2 id="read-the-state-before-the-traces">Read the state before the traces</h2>

Start from the missing proof step visible in the current goal, not from the raw
trace output.

Ask first:

- which resource or fact should the next proof step come from
- whether the missing step is decomposition, normalization, extraction,
  cancellation, or discharge of a side condition
- whether the transition looks merely surprising or whether it actually loses
  useful information

This usually gives better signal than staring at the last failed tactic in
isolation.

## Common explanations

- **Wrong search path or phase**:
  the automation never reaches the phase you expected, or reaches it too late
  to matter.
- **Blocked side condition**:
  a small pure obligation, typing fact, or validity fact prevents a much larger
  continuation from moving.
- **Missing hint or ordinary lemma**:
  the search is in the right area, but lacks a needed local fact, hint, or
  bridge lemma.
- **Information-losing transition**:
  rewriting, cancellation, or existential instantiation changes the goal in a
  way that makes the intended proof path much harder or unprovable.
- **Not actually an automation issue**:
  the deeper problem lies in proof strategy, formalization choices, information
  hiding, or an outright semantic bug.

## Common case

The standard BRiCk debugging progression is:

1. let `go` advance the proof while it is still helping
2. stop once `go` is genuinely stuck or has made the state worse
3. inspect the resulting state and follow the
   [diagnosis loop](#core-workflow)
4. if the state alone is not enough, use `with_log!` to generate
   [Debug Traces for Automation](../../../reference/skylabs.auto/)

During exploratory proofs, or while developing automation for a new
abstraction, try the smallest local remediation first: manual unfolding,
rewriting, decomposition, or one-off bridge steps can all help explain the
blocker before you change the automation itself.

## Candidate next actions

- [Debug Traces for Automation](../../../reference/skylabs.auto/):
  commands, flags, invariants, and variants for `Set Typeclasses Debug`,
  `Set SL Debug`, and `with_log`.
- [Proof Strategy Gotchas](./proof_strategy_gotchas.md):
  when the state is technically consistent, but the proof has drifted onto a
  much rougher path than the surrounding tactics and automation are designed to
  support.
- [Dealing with Missing Type Instances](./missing_type_instances.v):
  a concrete resolution page for one common automation failure mode.
