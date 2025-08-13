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
iExists _.
iSplit.
Abort.

(*@HIDE@*)
End with_cpp.
(*@END-HIDE@*)

