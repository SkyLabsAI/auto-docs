---
title: Automatic Fractional Splitting
key: bluerock.auto.cpp.auto_frac.hints
---
(*|
This file provides hints based on `AsFractional` and `AsCFractional` and meant to automate fractional splitting,
recombining and the picking of fractions.

It uses the typeclasses `Recombine(C)Frac`, `Half(C)Frac` and `(C)FracDiff` to parse fraction terms and symbolically calculate
the sum of fractions (including `cQp.t`), subtraction of fractions and halving as well. Subtraction is calculated symmetrically
in such a way that we don't need to know for sure which fraction is greater than the other.

The hints proper are:
- `recombine_(c)frac_F`
- `recombine_(c)frac_same_F`
- `split_specific_(c)frac_C`
- `pick_(c)frac_and_split_C`

They are meant to recombine premises whenever possible, cancel conclusion terms where the fraction is know and and
picking a safe choice for a fraction when fractions are existentially quantified. The hints are prioritized in
such a way that we parcel out all the fractions that are known before instantiating existential quantifiers.

Work in progress: the classes for parsing and normalizing fractions are provisional. They are expected to be brittle and slow
  and a solution based on more complete reflection is in the works.

Limitations: the fraction picking hints are robust in the face of a need to split the same premise repeatedly any
  number of times but for existentially quantified fractions that are referenced in multiple terms, the choice will
  not take that fact into consideration. For that reason, fraction picking hints are, at least at first, opt-in.
|*)
