---
title: "Debug Traces for Automation"
key: "automation-debug-traces"
availableFrom: "skylabs.auto"
eleventyNavigation:
  title: "Debug Traces for Automation"
  order: 120
---

## Key ideas

SkyLabs automation debugging usually combines two complementary traces:

- Rocq's built-in typeclass-resolution trace, enabled with
  [`Set Typeclasses Debug`](https://rocq-prover.org/doc/master/refman/addendum/type-classes.html)
- BRiCk's structured Ltac2 trace, implemented by the
  [`ltac2-logger` module](https://github.com/SkyLabsAI/BRiCk/tree/master/ltac2-logger)
  and enabled with `Set SL Debug ...`

`with_log` and `with_log!` then run one tactic invocation and show the
structured BRiCk trace for that run. For diagnosis workflow and interpretation,
start with
[Diagnosing Surprising or Incorrect Proof-State Transitions](../docs/common_errors/automation_debugging.md).

Use this page when you already know you want the command-level reference:

- [Common case](#common-case)
- [Invariants](#invariants)
- [Choosing the trace setting](#choosing-the-trace-setting)
- [What each trace is good for](#what-each-trace-is-good-for)
- [Useful variants](#useful-variants)

## Common case

For BRiCk end-users, the standard one-shot debugging recipe is:

```rocq
repeat (progress go).
(* HERE: [go] is genuinely stuck. *)

Set Typeclasses Debug.
Set Typeclasses Debug Verbosity 3.
Set SL Debug "@default=3".
with_log! work.

Unset SL Debug.
Unset Typeclasses Debug.
```

This captures three complementary views of the same state:

- the proof state itself
- Rocq's typeclass-resolution trace
- BRiCk's structured trace for the automation run

`with_log! work` is the common default after `go` gets stuck because `work`
uses the separation-logic and typeclass hints without continuing to step the
`wp` layer as aggressively as `go`.

For other instrumented tactics, keep the same pattern but replace `work` with
the tactic whose behavior you want to inspect.

## Invariants

### Set `SL Debug` before any `with_log`-style command

`Set SL Debug ...` must be in place before you call `with_log`, `with_log!`,
`with_log_file`, `with_log_tmp_file`, or similar tactics. Otherwise the
structured trace may produce no useful events.

### Capture both traces from the same state

Run `Set Typeclasses Debug ...` and the `with_log`-style command from the same
state you are trying to diagnose. If you mutate the state first, the traces
stop being comparable.

### Bracket debugging settings locally

Prefer short `Set ...` / `Unset ...` blocks around the debugging command. Avoid
leaving `Typeclasses Debug`, `SL Debug`, or other exploratory settings enabled
after the local investigation is over.

### Prefer one-shot tracing over accumulated tracing

Use `with_log`-style tactics rather than enabling direct printing by default.
`with_log!` resets the trace state, runs one tactic invocation, and prints one
trace.

## Choosing the trace setting

Start with:

```rocq
Set SL Debug "@default=3".
```

Escalate when needed:

- `Set SL Debug "@all=3".` when the interesting events are likely behind
  development-only flags
- `Set SL Debug "@all=10".` when you need a very noisy internal trace

If you are not seeing anything useful, `Print Ltac2 Log Flags.` can tell you
which flags are available and whether the extension exposed them as ordinary
flags or dev flags.

## What each trace is good for

### `Set Typeclasses Debug`

This is Rocq's built-in trace for typeclass resolution. It tells you:

- which class obligations are being searched for
- which hints and instances Rocq tries
- where search branches fail or get shelved

Reference: [Rocq reference manual, typeclasses](https://rocq-prover.org/doc/master/refman/addendum/type-classes.html).

### `with_log` and related tactics

This is BRiCk's structured trace. It is most useful for:

- seeing which top-level search families were attempted
- understanding whether the automation is in a forward, backward, cancellation,
  normalization, or similar phase
- identifying where the search got far enough to matter and where it never
  entered the expected phase at all

Reference surface:

- [`ltac2-logger` module in BRiCk](https://github.com/SkyLabsAI/BRiCk/tree/master/ltac2-logger)
- [Exploring Programs in Logic](../docs/debugging/main.v)

## Useful variants

### Expected failure

If the debugging command is expected to fail, prefix it with `Fail` so the
trace still appears without breaking the surrounding proof script:

```rocq
Set SL Debug "@all=3".
Fail with_log! work.
```

### Timeout-bounded debugging

If the tactic may loop or simply run too long, wrap the debugging call in a
timeout:

```rocq
Set Typeclasses Debug.
Set SL Debug "@all=3".
Timeout 1 with_log! work.
```

or:

```rocq
Set Typeclasses Debug.
Set SL Debug "@all=3".
with_log! timeout 1 work.
```

### File output for large traces

When the notice buffer becomes unwieldy, write the trace to a file instead:

```rocq
Set SL Debug "*=100".
with_log_file "/tmp/log.html" ework with id.
```

File output supports `.txt`, `.json`, and `.html`; `.html` is often the
easiest format to inspect for long structured runs.

### Direct printing

`Set SL Direct Log.` prints events as they are recorded instead of collecting a
one-shot trace.

Use it for exploratory live investigation. Do not make it your default
debugging mode when you want a clean, comparable trace for one tactic call.
