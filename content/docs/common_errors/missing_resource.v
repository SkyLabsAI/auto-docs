(*@HIDE@*)
Require Import bluerock.auto.cpp.prelude.proof.
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.
(*@END-HIDE@*)
(*|
# Dealing with Missing Resources

Sometimes, a proof will get stuck because you are missing some
{{ "resource" | terminology }}.

To show this problem, we will try to verify the following `inc_i` function:
|*)
cpp.prog source prog cpp:{{
  void inc_i(unsigned int &i) {
    i++;
  }
}}.

(*@HIDE@*)
(* TODO upstream! *)

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context {σ : genv}.

(* TODO: add to proof prelude. *)
Import linearity.

Tactic Notation "wAdmit" uconstr(R) := iAssert (R : mpred)%I as "-#?"%string; first admit; rewrite ?bi.affinely_elim.
(*@END-HIDE@*)

(*|
Assume we try proving this function fits the following (incorrect) spec.
|*)
Section with_inc_i.
  cpp.spec "inc_i(unsigned int &)" from source as inc_i with (
    \arg{i_r} "i" (Vref i_r)
    \post emp).

  Lemma inc_i_ok : verify[source] inc_i.
  Proof.
    verify_spec.
    go.
(*|
This proof gets stuck on the following goal:
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
          (Kcleanup source [] (Kreturn (λ v0 : ptr, ▷ _PostPred_ v0))))) ∗
    i_r |-> uintR 1$m v
```

Here, the goal is a separating conjunction where the first conjunct is the
program continuation (it involves a `wp`), and the second is the resource
that the automation cannot find --- `i_r |-> uintR 1$m v`, that is ownership of the memory that `i_r` points to.

To continue exploring our proof, we can try to add `wAdmit R` to continue, even if eventually we need a proper fix.

In cases like these, when the automation cannot find some resource `R`, it's for one of two reasons.

- Either we forgot `R` from our precondition,
- or we _do_ own `R` but it is hidden in some assumption `S` that the automation cannot unfold.

In the first case, we can add `\pre R` to our function precondition and restart our proof.
In the second case, we can either unfold `S` by hand, or add some unfolding hints.

Coming back to our proof,
|*)
    wAdmit (Exists v, i_r |-> uintR 1$m v).
    go.
(*|
Here, our proof ends up being stuck with an extra assumption;
```coq
  _ : i_r |-> uintR 1$m (trim 32 (v + 1))
  --------------------------------------∗
  emp
```

In this case, the proper fix is to add this assumption to the postconditions.
|*)
  Abort.
End with_inc_i.

(*|

|*)
cpp.spec "inc_i(unsigned int &)" from source as inc_i_fixed with (
  \arg{i_r} "i" (Vref i_r)
  \pre{v} i_r |-> uintR 1$m v
  \post i_r |-> uintR 1$m (trim 32 (v + 1))).

Lemma inc_i_ok : verify[source] inc_i_fixed.
Proof.
  verify_spec.
  go.
Qed.

(*@HIDE@*)
(* TODO: later, add pointers about (lazy) unfolding. *)
End with_cpp.
(*@END-HIDE@*)

