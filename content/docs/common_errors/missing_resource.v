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
that the automation cannot find --- `i_r |-> uintR 1$m v`.

To continue exploring our proof, we can try to add `wAdmit R` to continue; but eventually we need a proper fix.

In cases like these, when the automation cannot find some resource `R`, it's for one of two reasons.

- Either we forgot `R` from our precondition,
- or we _do_ own `R` but it is hidden in some assumption `S` that the automation cannot unfold.

In the first case, we can add `\pre R` to our function precondition.
In the second case, we can either unfold `S` by hand, or add some unfolding hints.
|*)

(*|
# If we are missing resources

In the first case, we can unfold `S`
# Find the resource in our context
|*)
(* TODO: elsewhere, explain anatomy of a goal, split in existentials and conjunctions. *)

(*|
When the automation ownership of some resource `R`, we either _do_ own `R`
The right fix will be one of these options:
- sometimes, we _do_ won `i_r |-> uintR 1$m v`.
The usual fixes are as follows:
|*)

(*@HIDE@*)
Import iris.proofmode.environments.
Ltac clippy_goal E G :=
  (* idtac G; *)
  lazymatch G with
  | bi_exist _ =>
    (* idtac G; *)
    idtac "Goal is an existential, using `iExists _` to progress";
    iExists _
  | bi_sep ?A ?B =>
    idtac "you might need either " A " or " B;
    iSplitL
  | _ => idtac "backtrack"
  end.

Ltac clippy :=
  lazymatch goal with
  | |- envs_entails ?E ?G =>
    (* idtac E G; *)
    clippy_goal E G
  | _ => idtac
  end.
(* Ltac clippy1 := iExists_. *)
(* Succeed clippy1. *)
(* Ltac clippy2 := *)
(*   lazymatch goal with *)
(*   | |- envs_entails _ (bi_exist _) => *)
(*     idtac "iExists"; *)
(*     iExists_ *)
(*   | |- _ => idtac "backtrack" *)
(*   end. *)
(* Succeed clippy2. *)

(*

TODOs:
- a better clippy could use TC search to inspect the goal more cleverly,
  recognize and ignore the program continuation (wands and WPs), and suggest what's missing.
- SkyLabs could provide AI assistance here


 *)

    Import MyPretty.
    work.

clippy.
pretty.
(*@END-HIDE@*)

(* TODO: explain syntax of separation logic *)
iExists 0%Z.
wAdmit (i_r |-> uintR 1$m 0).
wAdmit (Exists z, i_r |-> uintR 1$m z).
wAdmit (Exists z, i_r |-> uintR 1$m z).
clippy.
clippy.
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
(* Tactic Notation "wAdmit" uconstr(R) := iAssert (R) as "-#?"%string; first admit. *)
(* wAdmit (∃ z, i_r |-> uintR 1$m z). *)
(* wAdmit (∃ z, i_r |-> uintR 1$m z)%I. *)
(*@END-HIDE@*)

