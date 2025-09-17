---
title: The `verify` notation
key: bluerock.auto.cpp.cpp_proof
---
(*|

The `verify[ tu ] spec` provides a convenient way to write
theorem statements for proofs that automatically computes the
dependencies, which are the specifications of functions called by
the function being verified.

If dependencies might be missing, you can use
`verify?[ tu ] spec` to ignore missing-specification errors.

When the context contains an assumption of the form `<module ⊧ σ`, one can
write `verify[_]` (or `verify?[_]`) to automatically infer `module`.

```coq
Lemma ctor_ok : verify[ module ] ctor_spec.
Proof. ... Qed.
```
|*)
