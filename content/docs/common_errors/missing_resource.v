(*@HIDE@*)
Require Import bluerock.auto.cpp.prelude.proof.
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.
(*@END-HIDE@*)
(*|
# Dealing with Missing Resources

Sometimes, a proof will get stuck because you are missing some
{{ "resource" | terminology }}.
For instance:

```cpp
void missing_spec() {}
void test() {
  missing_spec();
}
```

|*)
cpp.prog source prog cpp:{{
  void inc_i(unsigned int &i) {
    i++;
  }
}}.

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context `{MOD : source ⊧ σ}.

  cpp.spec "inc_i(unsigned int &)" as inc_i with (
    \arg{i_r} "i" (Vref i_r)
    \post emp).

(* TODO upstream! *)
Tactic Notation "wAdmit" uconstr(R) := iAssert (R : mpred)%I as "-#?"%string; first admit.
(*@END-HIDE@*)

(*|
When we start our proof, `verify?` complains that it can not find a specification of `missing_spec()`, so we're aware of the problem.
 |*)
Lemma inc_i_ok : verify[source] inc_i.
Proof.
  verify_spec.
  go.
(*|
```coq
  _ : denoteModule source
  _ : type_ptr "unsigned int&" i_addr
  --------------------------------------□
  _ : PostCond
  _ : i_addr |-> refR<"unsigned int"> 1$m i_r
  --------------------------------------∗
  ∃ v : Z,
    (i_r |-> uintR 1$m (trim 32 (v + 1)) -∗
      interp source 1
        (wp_block source [region: "i" @ i_addr; return {?: "void"}] []
          (Kcleanup source [] (Kreturn (λ v0 : ptr, ▷ _PostPred_ v0))))) ∗ i_r |-> uintR 1$m v
```
This goal is hard to read, but it is stuck because we are missing `i_r |-> uintR 1$m v`.
|*)
(* Tactic Notation "wAdmit" uconstr(R) := iAssert (R) as "-#?"%string; first admit. *)
(* wAdmit (∃ z, i_r |-> uintR 1$m z). *)
(* wAdmit (∃ z, i_r |-> uintR 1$m z)%I. *)
(* TODO: explain syntax of separation logic *)
wAdmit (Exists z, i_r |-> uintR 1$m z).
(* TODO: explain syntax of separation logic *)
(* iExists 0%Z. *)
wAdmit (i_r |-> uintR 1$m 0).
go.
Abort.


(*|

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

