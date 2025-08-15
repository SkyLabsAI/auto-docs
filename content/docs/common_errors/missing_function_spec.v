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
Require Import bluerock.auto.cpp.prelude.spec.
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
  Tactic Notation "wAdmit" uconstr(R) := iAssert (R : mpred)%I as "-#?"%string; first admit; rewrite ?bi.affinely_elim.
(*@END-HIDE@*)

(*|
When we start our proof, `verify?` complains that it can not find a specification of `missing_spec()`, so we're aware of the problem.
 |*)
Lemma test_ok : verify?[source] "test()". (* TODO: fix this + error message*)
Proof.
  verify_spec.
  go.
  (*|

  The automation is stuck verifying the following goal – the invocation of the function
  `missing_spec()`; the function name is visible in the `inl (Vptr (_global "missing_spec()"))`.

  ```coq
    _ : denoteModule source
    --------------------------------------□
    _ : PostCond
    --------------------------------------∗
    wp_invoke_O source "void()"
      (inl (Vptr (_global "missing_spec()"))) [] None
      (λ _ : val,
        interp source (1 >*> 1)
          (wp_block source [region: return {?: "void"}] []
              (Kcleanup source [] (Kreturn (λ v : ptr, ▷ _PostPred_ v)))))
  ```

  ## Solution #1: Mark the function for inlining

  If this function is trivial, or we don't want to write specification right now,
  we can simply mark the function for inlining with the `cpp.spec ... inline`,
  and continue the proof with `go`.

  Here, since "missing_spec()" is a no-op, this is enough to complete the proof.
  |*)
  (*@HIDE@*)
  (*|
  (see ... for more information).
  |*)
  (*@END-HIDE@*)
  cpp.spec "missing_spec()" inline.
  go.

  (*@HIDE@*)
  Undo 2.
  go.
  (* Goes back to before the cpp.spec command. `Undo 1`. doesn't do the right thing. *)
  (*@END-HIDE@*)

  (*|
  ## Solution #2: Add a Specification

  However, many functions are not trivial, so a specification is preferred over
  inlining, or even required.

  We can define spec `missing_spec_spec` as usual, but actual specs are _not_
  immediately available to the automation. We have two options to fix that.
  |*)
  (*@HIDE@*)
  (*|
  (see ... for more information).
  |*)
  (*@END-HIDE@*)

  cpp.spec "missing_spec()" as missing_spec_spec with (\post emp).
  Fail progress go.

  (*|
  ### Option a: add the proof to the context locally

  While exploring the proof, to continue the proof without starting over, we can
  use `wAdmit missing_spec_spec` to add it to our proof context, and complete
  our goal with `go`. However, proofs using `wAdmit` are "incomplete" and cannot
  be closed with `Qed`.
  |*)
  wAdmit missing_spec_spec.
  go.
  Fail Qed.
  Admitted.

  (*|

  ### Option 2: Move the Spec above the Proof and Restart it

  The easiest thing to do is to introduce this specification above the proof and
  restart it; `verify?` or `verify` will then find the new spec and add it to the context.
  |*)

  (*|
  ## Cleaning up

  All these options can be useful while developing a proof.

  But once we complete the proof with the correct spec, you'll want to move the
  `cpp.spec` command together with other specs, so that all those specs are
  available to other clients.
  |*)

(*@HIDE@*)
End with_cpp.
(*@END-HIDE@*)
