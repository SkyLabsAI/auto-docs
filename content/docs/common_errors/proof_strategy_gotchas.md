---
title: "Proof Strategy Gotchas"
layout: page
eleventyNavigation:
  key: proof-strategy-gotchas
  title: "Proof Strategy Gotchas"
  parent: troubleshooting
  order: 140
---

<p class="small text-body-secondary mb-3">
Assumes you are already comfortable reading BRiCk proof states and switching
between ordinary Rocq tactics and SkyLabs automation when needed.
</p>

On this page, we focus on proofs in which the progress is slower or more
tortuous than one would expect. Sometimes, it happens because, although a
given proof plan can be enacted in multiple ways, each one may not be equally
well supported by the Skylabs automation. At other times, automation support
exists for our chosen technique, but the automation needs information about
some of our predicates, functions or types in order to make use of them. At
other times still, our proof state has multiple arithmetic expressions that are
provably equal but their syntactic differences prevent the automation from
using the two together.

## Practical heuristic

If a locally valid step suddenly makes the proof feel much harder or less ergonomic, treat that as
signal. Back up to the last clean state, identify the kind of proof you are in,
and try the smallest next step that fits it before widening scope or repairing
the rest of the proof around an awkward state.

## When to suspect this

Use this page when:

- the proof advances, but the resulting state becomes much harder to read or
  stabilize
- a locally reasonable step causes automation to stop helping
- the state no longer resembles the proof shape that the surrounding tactics
  appear designed to support
- the blocker seems to be the chosen proof path rather than a missing import,
  missing instance, or malformed tactic

## Action loop

1. back up to the last clean state
2. identify the kind of proof you are in
3. ask which tactic style normally carries that proof family
4. try the smallest step that better fits that proof before repairing the
   awkward state in place

A proof strategy issue is often not a missing fact, but a misaligned choice of
tactic style, decomposition order, or induction style.

## Iris-heavy proofs

See [External Resources](../../further-reading.md) for the main Iris and
separation-logic references.

Prefer SkyLabs automation when it already supports the reasoning step you need.
For BRiCk-heavy separation-logic proofs, automation-driven steps usually compose
better with the expected proof shape than a heavily manual IPM script.

If Iris proof mode is needed, use it judiciously. Common tactics such as
`iFrame`, `iDestruct`, and nearby bookkeeping steps are usually enough.
Large manual IPM detours often produce states that are harder to hand back to
the automation cleanly.

Iris proofs mix ordinary Rocq reasoning with separation-logic proof mode, so a
plain Rocq step can be formally legal while still producing terms or contexts
that compose poorly with later Iris reasoning or SkyLabs automation.

### Warning: named spatial premises

SkyLabs automation will not cancel or otherwise process named spatial
resources, so the automation can appear stuck even when it could still make
progress on an anonymous or re-framed version of the same state.

### `induction`

Plain `induction` on an Iris obligation can sometimes work, but it often yields
unwieldy terms, context shapes, or proof-state transitions that do not
interact cleanly with the rest of the proof. When the proof is fundamentally
inside Iris proof mode, prefer the Iris-oriented path rather than forcing
ordinary Rocq induction deeper than it wants to go.

## `cpp.spec` weakest-precondition proofs

In `cpp.spec` and other weakest-precondition proofs, the next real blocker is
not always where the editor makes your eye land first. A large spatial
conclusion near the top of the screen may really be a continuation or weakest
precondition that cannot move until a small pure side condition, validity fact,
or typing fact near the bottom is discharged.

Before changing automation or rewriting the whole proof, inspect the full goal.
If the first large conclusion is really a continuation, the right next move may
be to discharge a small side condition first, not to attack the large spatial
goal directly.

## Candidate next actions

- [Diagnosing Surprising or Incorrect Proof-State Transitions](./automation_debugging.md):
  when the main issue is how automation changed the state, not the proof path
  you chose.
- [Debug Traces for Automation](../../../reference/automation-debug-traces/):
  when the proof state alone is not enough and you need the concrete trace
  commands, flags, or output modes.
