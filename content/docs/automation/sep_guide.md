---
title: "`sep` Tactic guide"
tags:
- learn
requires: []
provides:
- automation
eleventyNavigation:
  order: 202
  parent: learn
---


# Automation

The automation is structured in around proving separation logic entailments.
This means goals of the following form:

   P |-- Q

Where `P` and `Q` are formulas in separation logic.

## Guiding Principles

There are several guiding principles that we apply when developing automation.

  1. Robustness. Automation should be, as much as possible, agnostic to
     the associativity and commutativity of separating conjunction as well
     as names of variables.
  2. Conservative. Automation should be conservative, and strive to avoid
     reducing provable goals to unprovable ones. There are some instances
     where conservativeness is sub-optimal, but in general it enables users
     to build off the common foundation without having to worry about being
     "bitten" by it being "too clever".
  3. Extensible. While the core automation should have a good handle of
     primitive constructs, it is essential that the automation support
     extensions to teach it how to reason about user-defined predicates.

Violations of these principles should be reported as bugs unless they
are explicitly documented.

## A Basic Algorithm

Just given the rules of logic, we know that a simple way to prove an entailment is by reflexivity.

    ----------- REFL
      P |-- P

Separation logic admits a simple heuristic solver based on cancellation.
The primitive rule is the following:

           P |-- Q
    --------------------- FRAME
      R ** P |-- R ** Q

which allows us to drop common elements from the left- and right-hand
sides of the turnstile.

Using only this rule (and the structural rules of separation
logic[^fn-structural-rules], the following, very naive, algorithm is
sufficient for solving many goals.

  1. For each top-level atomic (i.e. not *syntactically* containing a
    `**`) formula (`P`) to the left of the turnstile, make the left hand
    side of the form `P ** F` for some `F`
  2. Do the same for the right hand side, writing the right hand side of the
     form `Q ** F'`.
  3. If `P` and `Q` are unifiable, use *FRAME* to remove the common conjuncts
     reducing the goal to solve the (smaller) entailment `F |-- F'`.
     If the head formulas are not unifiable, then try another permutation.

## Extensibility

While *FRAME* is sufficient to solve most simple entailments, the assumptions and conclusions do not always line in a way that enables using the rule directly. This is particularly true when entailments involve user-defined predicates such as representation predicates for custom data structures or concurrency constructs such as invariants.

In general, facts in our separation logic are expressed through entailments between predicates. For example, a predicate might be built up of several pieces, such as the representation predicate for the [`Point` class](../../tests/class/Point.hpp). Some other examples, in simpler notation, are the following:

```coq
Pair (a,b) p |-- ptsto p a ** ptsto (p+4) b
ptsto p a ** ptsto (p+4) b |-- Pair (a,b) p
List ls p ** [| ls = nil |] |-- [| p = nullptr |]
List ls p ** Exists x xs, [| ls = x :: xs |] |-- Exists nxt, ptsto p (x, nxt) ** List xs nxt
```

We will refer this style of writing lemmas as their "natural presentation" because it is a minimal characterization of the fact. In particular, the fact mentions only the relevant assertions, there are no extra pieces to muddy the waters.

### Term Orderings

While the natural presenation is simple to work with manually, it doesn't obviously provide a way to turn these facts into *efficient* automation. Generally, saturation is the decision procedure that we are going to use, but computing saturating sets is too expensive in practice. To make it more efficient, we need a term ordering that tells us when we are making progress. A "term ordering" gives a partial ordering to terms that describes when one term is more canonical than another. If we can set up an ordering such that if two formulas are equivalent then they have the same canonical form, then we can implement our decision procedure by simply canonicalizing both sides of the entailment and checking that the two are syntactically equivalent[^fn-canonical].

### Expressing Term Orderings in Lemmas

Rather than explicitly defining a term ordering which can be slightly uninitive, we instead express the term ordering implicitly through the lemmas that we provide to the automation. There are three types of lemmas:

1. *Forward Lemmas* reduce the left-hand side of the turnstile to a simpler form.
2. *Backward Lemmas* reduce the right-hand side of the turnstile to a simpler form.
3. *Cancellation Lemmas* reduce both sides simultaneously.

To avoid having to explicitly apply the frame rule everywhere and provide more flexibility in our rules, we use explicit framing in lemmas that we provide to automation. Clients of the automation can teach the automation rules to apply during by supplying variations on the *FRAME* rule above. In general, the structure of these rules is the following where `P`, `Q`, `P'`, and `Q'` are concrete, i.e. not universally quantified.

        ... side conditions ...
        P' ** F |-- Q' ** G
     ---------------------------
         P ** F |-- Q ** G

We call `P` the *forward trigger* because this rule will only "fire" if `P` occurs syntactically on the left-hand side of the entailment.
Similarly `Q` is the *backward trigger*.
Both `P` and `Q` are optional, but at least one must be present. If both are present, then the lemma is a cancellation lemma, if only `P` is present, then it is a forward lemma, and if only `Q` is present then it is a backwards lemma.
`F` and `G` are the frames for each side must occur unconstrained in the formula[^fn-unconstrained-frames].



To understand how rules like this can be used, we take the first example formula above describing the pair predicate.

```coq
pair (a,b) p |-- ptsto p a ** ptsto (p + 1) b
```

Using only the definition of this predicate, we can phrase the following rule for reading the first component of a pair.

    ptsto (p + 1) (snd x) ** F |-- G
    --------------------------------------- RD-FST
    pair x p ** F |-- ptsto p (fst x) ** G

Note that this rule follows straight-forwardly from the implication additionally encodes the information that the entailment above the line is more canonical than the entailment below the line. Note that this rule will generally be used when the code reads the first component of a pair and it implicitly opens the abstract pair predicate (which occurs below but not above the line).

**Exercise**: A similar rule can be used to allow the reading of the second component of a pair. Try to write it.

**Forward Lemmas** Sometimes, useful information can be gained simply by noticing some symbol on the left-hand side. An example of this might be the well-typedness of a variable.

    (is_int v -> ptsto x (tint v) ** F |-- F')
    -------------------------------------------- LEARN-PTSTO-INT
    ptsto x (tint v) ** F |-- F'

This lemma expresses the fact that if `x` points to an integer (`v`), then `v` must be a valid integer, e.g. in bounds of the type. Intuitively, the automation finds a place where it can apply the rule and then introduces the assumption `is_int v` into the Coq context. Similar styles can be used for introducing new variables, e.g.

    (forall v, v < 10 -> P v ** F |-- F')
    --------------------------------------
    PRED v ** F |-- F'

To avoid these forward lemmas being applied repeatedly, thus driving the automation into an infinite loop, the automation has some heuristics to ensure that forward lemmas introduce facts that were not previously provable.

**Backwards Lemmas** The converse of forwards lemmas are backwards lemmas. Backwards lemmas, are purely goal directed, caring only about a conjunct on the right-hand side of the entailment. The most common sort of backwards reasoning that we perform is weakest pre-condition computation which simplifies the structure of `wp` facts in the conclusion. Note, however, rules for function calls, for example, are actually better phrased as cancellation lemmas where the forward trigger is keyed on the function's specification.

## Side Conditions

Beyond the simple structure, the automation also permits side conditions which can be especially helpful for reasoning about disjunctive types. For example, a simple linked list.

```coq
llist ls p :=
  ([| ls = nil |] ** [| p = nullptr |]) \\//
  (Exists x xs p', [| ls = x :: xs |] ** ptsto p (x, p') ** llist xs p')
```

Ignoring the details of the recursive structure of this definition we note that there are two cases, the empty list and the non-empty list. Given a small amount of additional information, we can expose additional structure on this list. For example, the following lemma simplifies the predicate when the list is known to not be empty.

    p <> nullptr
    (forall x xs nxt, l = x :: xs -> ptsto p (x, nxt) ** llist xs nxt ** F |-- F')
    --------------------
    llist l p ** F |-- F'

Side conditions (e.g. `p <> nullptr` above) are discharged by user-extensible tactics (currently `work_tac`).

Note that all assumptions besides the last (which is expected to be an entailment) are treated as side-condition and therefore *must* be solved completely by the automation.


## Iterated Triggers

In rare instances it is necessary to match multiple conjuncts on the right- or left-side, i.e. either the forward or backward trigger is non-atomic. This can be expressed using separation logic side conditions. As an example, `A ** B |-- X` for *concrete* `A`, `B`, and `X` can be applied using the following forward lemma.

     F |-- B ** F'      <-- treated as a side-condition
     X ** F' |-- G
     ----------------
     A ** F |-- G

Due to the way that `True` works in separation logic, we can also find duplicable assertions and use them without cancelling them.

     F |-- B ** True      <-- treated as a side-condition
     X ** F |-- G
     ----------------
     A ** F |-- G

If `B` is a persistent fact, then information from it can be used in the entailment without needing to consume the resource. Furthermore, the automation understands `True` and will immediately solve any goal with an `True` on the right hand side.

*N.B.*: Due to the specifics of how the automation works, it is best to phrase iterated triggers using the most discriminating triggers first. For example, if `A` occurs much more frequently than `B`, the first of the examples should be phrased with `B` and `A` exchanged.

Exercise: Write reasoning lemmas to expose the following fact to the automation: `A ** B ** C |-- D ** E`. Orient it as each of a cancellation lemma, a forward lemma, and a backward lemma.

## Existential Quantifiers

Existential quantifiers occur frequently and can be a source of difficulty for automation due to the implicit information of the context. Furthermore, because existential quantifiers crop up so frequently, it is difficult to describe a single rule that will apply all the time. In general, the best automation avoids exposing existential quantifiers and instead exposes abstract predicates capturing how the automation should proceed.

An example of this is the rules for evaluating *partial* unary operators

      Exists r, [| eval_uop Neg x r |] ** Q r |-- wp (-x) Q

If the automation applies this rule naively and then instantiates the existentailly quantified `r` using a unification variable, then the automation must resolve `r` within the context of the exteistential.

An alternative is to convert this into a lemma with a side-condition and otherwise leave the `wp` uninterpreted.

     eval_uop Neg x r
     F |-- Q r
     ------------------
     F |-- wp (-x) Q

While morally the same, the side condition on this rule means that the existential quantifier in the above rule is never exposed to the automation which removes the possibility of the automation picking too restrictive of a context.

# Implementation

The core of the current automation is implemented in `Cpp.Auto.Discharge`. It uses an Ltac implementation of permutation for both sides of the entailment. The algorithm is implemented in `perm_left` and `perm_right`.

## Manual Reasoning

There are three useful tactics implemented in `Cpp.Auto.tactics` for using cancellation, forward, and backwards lemmas.

  - `cancel H` applies `H` as if it were a cancellation lemma
  - `fwd H` applies `H` as if it were a forward lemma
  - `bwd H` applies `H` as if it were a backward lemma

`_` variations of these tactics (i.e. `cancel_`, `fwd_`, `bwd_`) take a tactic used to solve side-conditions and use `simple eapply` rather than `eapply` to better simulate the conditions of the automation.

  - `cancel_ tac H`
  - `fwd_ tac H`
  - `bwd_ tac H`

## Extension Points

### `sl_opacity` Hint Database
Currently, the automation exposes one hint database to enable these sorts of lemmas. This database is called `sl_opacity` and it contains hints for forward lemmas, backward lemmas, and cancellation lemmas.

There exist several legacy databases that are still being searched by the automation for backward compatibility reasons. Some are listed below.
  - `cancel` contains cancellation lemmas
  - `fwd` contains forward lemmas
  - `bwd` contains backwards lemmas.

**Note** For performance reasons, `sl_opacity` deviates from Coq's default `Typeclass Opaque` settings. Hints not being applied because of that should be treated as a bugs. Hints can be added to their respective legacy database as a temporary workaround since those do have default `Typeclass Opaque` settings.

#### Footnotes

[^fn-canonical]: In its truest sense, canonicalization would include ordering terms and so also addresses associativity and commutativity, but for our purposes we will address associativity and commutativity through another mechanism that is internal to the automation.

[^fn:unconstrained-frame]: The reason for this restriction is that `perm_left` and `perm_right` guarantee nothing about the structure of the "rest" of the frame.
