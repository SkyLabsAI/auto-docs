---
title: Tactics for arithmetics
key: bluerock.auto.cpp.Arith
---
(*|
 Main tactics:
- `arith_solve` : solve (in)equalities. invokes lia after adding to the Rcoq context
  facts about the non-linear operations in the conclusion.
- `remove_useless_mod_a` : remove occurrences of `mod` (aka `trim`).
  This and the above are co-recursive.
- `mod_simpl` : uses modular (a `mod` b) reasoning to simplify goals.
- `norm` : fully normlize closed terms of selected types. often invoked as `norm numeric_types`
|*)
