---
title: Troubleshooting
layout: index-page
eleventyNavigation:
  key: troubleshooting
  order : 20
---

:::info
If you already know the issue family and just want a concrete page, use the
[contents](#contents) below. This page assumes you have
already worked through the [Quick Start](./quick-start.md) and at least enough
of [Learn](./learn.md) to be oriented in the normal proof workflow.
:::

Troubleshooting usually moves from explicit, localized tool feedback toward
more implicit, reasoning-derived, and potentially non-local findings:
- [**Categorize the Issue**](#categorize-the-issue):
  classify whether the problem is still local and tool-facing, or has become a
  deeper proof-time or semantic issue.
- [**Diagnose, Explain, and Evaluate**](#diagnose-explain-and-evaluate):
  start with the smallest local explanation and the smallest local experiment,
  then escalate to deeper candidate causes only after the simpler, more local
  ones have been explored, explained, or eliminated.
- **Propagate Fixes Incrementally**:
  validate locally before hoisting, generalizing, or widening scope;
  broader changes can induce churn, larger rebuilds, and unrelated breakage.

<h2 id="categorize-the-issue">Categorize the Issue</h2>

<p class="small text-body-secondary mb-3">
Rocq catches many issues during sentence processing, including typechecking.
Some of those checks rely on subtle mechanisms (e.g. <a href="https://rocq-prover.org/doc/master/refman/addendum/type-classes.html">typeclass-driven search</a>,
<a href="https://rocq-prover.org/doc/V9.2.0/refman/addendum/universe-polymorphism.html">conversion and unification</a>, and
<a href="https://rocq-prover.org/doc/master/refman/user-extensions/syntax-extensions.html">extensible notations and notation scopes</a>),
which can still produce syntactically valid but unexpectedly shaped terms.
</p>

### Local, Immediate Issues

- **Tool issues**:
  problems while preparing generated Rocq artifacts for C++ code, completing
  builds, using the editor environment, or working with the
  [scaffold tool](./scaffold/index.md). If you need to re-orient on the normal
  project flow, revisit the [Quick Start](./quick-start.md).
- **Syntax or typechecking issues**:
  failures while Rocq processes the next sentence, whether inside a proof or
  while defining terms, instances, sections, modules, or contexts. These often
  involve imports and namespaces,
  even when the immediate failure surfaces as a typechecking or lookup error.
- **Tactic failures**:
  Rocq feedback that a tactic sentence is not accepted, often because the
  tactic is malformed, the applied fact does not match the goal, or some local
  tactic invariant is violated.

### Deeper, Reasoning-Derived Issues

- **Proof issues**:
  some proof issues only become clear once you inspect the resulting state and
  the reasoning path that produced it.
  - [**Strategy gotchas**](./docs/common_errors/proof_strategy_gotchas.md):
    proof families with a clear happy path, where locally legal but
    poorly-aligned steps can make the rest of the argument much more manual,
    brittle, or opaque than it needs to be.
  - [**Surprising or incorrect proof-state transitions**](./docs/common_errors/automation_debugging.md):
    confusing, unexpectedly stuck, or incorrectly transformed proof states,
    including over-aggressive automation steps or bad existential
    instantiations that leave the remaining goals unprovable.
- **Modelling / Specification / Code Issues / Bugs**:
  mismatches in formalization style, information hiding, abstraction
  boundaries, or client-versus-implementer needs, as well as outright mistakes
  in reps, specs, or the underlying C++ code.

<h2 id="diagnose-explain-and-evaluate">Diagnose, Explain, and Evaluate</h2>

Prefer the smallest local explanation and the smallest local experiment first.
Start with the immediate messages from Rocq, `scaffold`, `dune`, or related
tools; if those do not fully explain the behavior, move toward reasoning-based
debugging of proof states, automation behavior, and upstream semantic choices.

- **Local tool feedback first**:
  separate parser, build, editor-environment, syntax, typechecking, and tactic
  failures from deeper proof-state causes before widening the debugging scope.
- **Proof issues**:
  once local sentence-processing failures are ruled out, decide whether the
  real problem is the proof path itself or the behavior of the resulting state.
  - [**Strategy gotchas**](./docs/common_errors/proof_strategy_gotchas.md):
    check whether the current proof family has a better-structured happy path
    before committing to a state that is technically valid but much rougher to
    finish.
  - [**Surprising or incorrect proof-state transitions**](./docs/common_errors/automation_debugging.md):
    inspect how the proof state evolved, compare it against what you expected,
    and evaluate the smallest candidate local fixes.
- **Modelling / Specification / Code Issues / Bugs**:
  check whether the real cause lies in formalization choices, information
  hiding, spec or rep phrasing, client-versus-implementer boundaries, or an
  actual bug in the model or the underlying C++ code.
