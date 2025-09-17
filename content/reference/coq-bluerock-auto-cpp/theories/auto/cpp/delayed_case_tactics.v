---
title: Join points
key: bluerock.auto.cpp.delayed_case_tactics
---
(*|
This file provides two tactics `wp_if` and `wp_switch`,  with variants,
for dealing with join points produced by `if` and `switch` statements.

- `wp_if` -- advance past a `branch.stmt` performing an immediate case split.
  This should only be used if the continuation is "simple".
- `wp_if wpp` -- `wpp` is a `region -> WithPrePost` (specify with function
  spec syntax) that describes the branches as a function with the given
  specification.  Unlike a function call, the branches get access to, but
  must preserve the frame.
- `wpe_if wpp` -- similar to `wp_if wpp` but applies to conditional expressions.
- `wpe_if PQ wpp` -- similar to `wpe_if wpp` but `PQ`, a `region -> mpred`,
  specifies a postcondition to be proved after freeing the temporaries of the
  enclosing expression.

- `wp_switch` -- same as `wp_if` but for `branch.cases`
- `wp_switch wpp` -- same as `wp_if wpp` but for `branch.cases`
- `wp_switch P` -- where `P` is a `region -> mpred` states that `P` is the
  (big-footprint) specification of the join point.
|*)
