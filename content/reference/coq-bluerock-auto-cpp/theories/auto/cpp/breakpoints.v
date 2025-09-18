---
title: Using breakpoints
key: bluerock.auto.cpp.breakpoints
---
(*|
Suggested uses of breakpoints:
1. resource splitting & ghost reasoning: stop the automation at exactly the right
  point to subdivide a physical resource (or do ghost reasoning, e.g. inserting
  a fupd and opening an invariant).
2. self-documenting workarounds for learning existentials: stop the automation just
  prior to a known-bad evar instantiation (subsequently instantiating it manually
  or using the learner to do so).
3. stepping over C++ statements using the automation
|*)
(*|
## `wuntil`
`wuntil pat tac` adds a breakpoint on the first match of `pat`, runs `tac`, and
then removes the first match of `BREAKPOINT pat`.
The breakpoint being removed might not be the one added, if `tac`
is doing something interfering with the breakpoints.

For example, the following call asks `go` to run and then stop before the function returns.
```coq
wuntil (Sreturn _) go.
```
|*)
(*|
## `wthrough`
`wthrough pat tac_body tac_post` adds a breakpoint on the first match of `pat`, at which point it:
1. attempts to progress to the new breakpoint using `tac_body`
2. removes the breakpoint
3. attempts to proceed using `tac_post`.
|*)
