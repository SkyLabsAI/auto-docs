(*|
In this section, we explain the semantics of our core automation tactics: `sep`,
and its wrappers like `work` and `go`.

`sep` simplifies or solves separation logic entailments `P ⊢ Q` via builtin
proof rules and user-defined Rocq hints.

1. apply introduction rules for universals and wands
2. then apply forward and backward hints to simplify assumptions and
conclusions, as far as possible
3. then apply learning hints to instantiate any existentials as far as possible
4. if enabled, instantiate any remaining existential quantifiers with evars
5. apply introduction rules for joint conjunctions
<!-- when? this seems the most reasonable point -->
6. then apply framing/identity cancellation, and cancellation hints as far as possible
7. restart from 1

The process terminates when no progress is possible or when the goal is solved.

# A quick tour

## Iris goals

`sep` works on Iris goals `Γ ; Γp ; Γs ⊢ Q`, where `Γ` is the Rocq context,
`Γp` is the intuitionistic context, `Γs` is the spatial context, and `Q` is the
conclusion.
In an Iris goal, assumptions in `Γp` can be duplicated or discarded
freely, unlike assumptions in `Γs`.

Iris assumptions can be named or anonymous; by default `sep` will preserve named
assumptions unchanged, but `$usenamed=true` will override this behavior.

`sep` will eliminate separating conjunctions in assumptions.

## Proof strategy

While manual proofs can introduce separating conjunctions by splitting the
context, `sep` does not attempt that, because that requires guessing how to
split the context correctly.

Instead, we can cancel spatial assumptions against conclusion conjuncts using
the following cancellation rule:
```
P1 ⊢~ P2              Γ ; Γp ; Γs ⊢ Q
-------------------------------------- CANCEL
Γ ; Γp ; P1, Γs ⊢ P2 ∗ Q
```

Applying this proof rule turns the goal `Γ ; Γp ; P1, Γs ⊢ P2 ∗ Q`
into a new goal `Γ ; Γp ; Γs ⊢ Q`, where the assumption `P1` has been cancelled
against the conjunct `P2` in the conclusion as long as `P1` entails `P2`,
possibly via hints (`P1 ⊢~ P2`).

`P1 ⊢~ P2` holds in two cases:
- `P1` and `P2` unify; then we talk about identity cancellation, which is
  essentially the frame rule
- `P1` entails `P2` via hints; then we just talk about cancellation

### Identity cancellation and unification

Unification in Rocq can unfold definitions, perform computation and instantiate
existential variables, but for efficient automation, we must restrict all these behaviors.

Unfolding arbitrary definitions can be very slow, but treating all definitions
as opaque can be too restrictive. Hence, we reuse Rocq's notion of hint opacity.

|*)
