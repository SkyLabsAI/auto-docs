(*|
# Dealing with Missing Function Specifications

Sometimes, a proof will get stuck because you are
missing a specification for a function that you are calling.
For instance:

```cpp
void missing_spec() {}
void test() {
  missing_spec();
}
```

|*)
(*@HIDE@*)
Require Import bluerock.auto.cpp.prelude.proof.
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.

cpp.prog source prog cpp:{{
   void missing_spec() {}
   void test() {
     missing_spec();
   }
}}.

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context `{MOD : source ⊧ σ}.

  cpp.spec "test()" with (
    \post emp).
(* TODO: text uses `verify?`, code uses `verify`. Align either way. *)
(*@END-HIDE@*)

(*|
When we start our proof, `verify?` complains that it can not find a specification of `missing_spec()`, so we're aware of the problem.
 |*)
Lemma test_ok : verify[source] "test()". (* TODO: fix this + error message*)
Proof.
  verify_spec.
  go.
(*|
```coq
  _ : denoteModule source
  --------------------------------------□
  _ : PostCond
  --------------------------------------∗
  invoke.wp_invoke_O.body source "void()" (* TODO: fix this *)
    (inl (Vptr (_global "missing_spec()"))) [] None
    (λ _ : val,
       interp source (1 >*> 1)
         (wp_block source [region: return {?: "void"}] []
            (Kcleanup source [] (Kreturn (λ v : ptr, ▷ _PostPred_ v)))))
```

The automation is stuck verifying this goal which is the invocation of the function
`missing_spec()`, which is visible in the `inl (Vptr (_global "missing_spec()"))`.

## Solution #1: Add a Specification

Ultimately, to do the verification, we will need a function specification. We can
write one in the normal way (see ... for more information).
|*)
cpp.spec "missing_spec()" as missing_spec_spec with (\post emp).
(*|
At this point, we have two choices. The easiest thing to do is to introduce this
specification above

### Choice 1: Restart the proof

just restart the proof.

### Choice 2: Manually add to the context

`wassume missing_spec_spec`?
use `iAssert`
|*)
iAssert (missing_spec_spec)%I as "-#?"%string; first admit.
go.

(*|
## Solution #2: Mark the function for inlining

If this function is trivial, or we don't want to write specification right now,
we can also simply mark the function for inlining (see ... for more information).
|*)
cpp.spec "missing_spec()" inline.
(*|
Unlike with the previous solution, we do not need to add anything to the context and now `go` will continue past the function call finishing the proof in this case.
 |*)
go.

Qed.
(*@HIDE@*)
End with_cpp.
(*@END-HIDE@*)
