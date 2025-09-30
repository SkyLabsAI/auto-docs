(*
 * Copyright (C) 2024-2025 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(**
Feedback:
maybe \arg belongs in a second lesson.
definitely valid belong there, addition can be a second lesson.
*)

(** * Overview
FILL IN.
 *)

(** Import the C++ verification environment *)
Require Import bluerock.auto.cpp.prelude.proof.
(** Define inline the code to be verifying *)
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.

cpp.prog module prog cpp:{{

unsigned add(unsigned x, unsigned y) {
        return x + y;
}
}}.


(**  Import the code that we are going to be verifying *)
(* Require Import bluerock.cpp.demo.basic.main_cpp. *)

(** interpret arithmetic operations and integer literals as [Z]. *)
#[local] Open Scope Z_scope.

Section with_cpp.
  (** Separation logic statements depend on an instance of the [cpp_logic] typeclass. *)
  Context `{Σ : cpp_logic}.

  (** Specs and proofs also require us to assume that the linked program [σ] contains
  the concrete AST [module] that we're doing proofs about.
  We know nothing else about the program. *)
  Context `{MOD : module ⊧ σ}.

  cpp.spec "add(unsigned, unsigned)" as add_spec with (
    \arg{x} "x" (Vint x)
    \arg{y} "y" (Vint y)
    \post[Vint (trim 32 (x + y))] emp).
  (** Here, we use the [cpp.spec] command to specify that function "add(int,
  int)" returns value [Vint (x + y)] when invoked on arguments [Vint x] and
  [Vint y], assuming that [Vint (x + y)] is a valid integer value (that is, assuming
  that addition doesn't overflow).

  This spec is equivalent to the following one:
  *)

  cpp.spec "add(unsigned, unsigned)" as add_spec' with (
    \with x
    \arg "x" (Vint x)
    \with y
    \arg "y" (Vint y)
    \post[Vint (trim 32 (x + y))] emp).
  (*
  Here, [\with x] quantifies over [x]: each call site can instantiate [x] with
  a different value.

  [\arg "cosmetic_name" (value_expression)] requires that the next function argument is equal to
  [value_expression], [\require (some_prop : Prop)] adds a pure precondition to
  the function spec, and [\post[return_value_expression] emp] specifies the
  return value equals [return_value_expression].

  When verifying client code like [int z = add(2, 4); program_rest] using this spec,
  we will have to prove something like
  <<
  Exists (x y : Z),
    [| [Vint 2] = [Vint x] |] **
    [| [Vint 4] = [Vint y] |] **
    ... (Vint (x + y))
  >>
  *)

  (** Next, we can prove that the [add] function in the [module] AST
  actually implements [add_spec].
  First, we state the lemma: *)
  Lemma add_ok : verify[module] add_spec.
  (* [verify[ast.module] spec] will produce the correct statement. *)
  Proof.
    verify_spec.
    go.
  Qed.

End with_cpp.

(** XXX compile errors cause warnings. *)
cpp.prog module1 prog cpp:{{

int add(int x, int y);

int doubled (int n)
{
  int a = n+1;
  int b = n-1;
  return add(a,b);
}

int quadruple_by_double (int n)
{
  int m = doubled(n);
  return doubled(n);
}

}}.

Section with_cpp.
  (** Separation logic statements depend on an instance of the [cpp_logic] typeclass. *)
  Context `{Σ : cpp_logic}.

  Context `{MOD : module1 ⊧ σ}.

  #[local] Open Scope Z_scope. (* XXX bug needed after each cpp.prog, hide this. *)
  cpp.spec "add(int, int)" as add_spec'' with (
    \arg{x} "x" (Vint x)
    \arg{y} "y" (Vint y)
    \require valid<"int"> (x + y)
    \post[Vint (trim 32 (x + y))] emp).

  cpp.spec "doubled(int)" as doubled_spec with
      (\arg{n} "n" (Vint n)
       \require valid<"int"> (2 * n)
       \post[Vint (2 * n)] emp).

  (** Next, we can prove that the [add] function in the [module] AST
  actually implements [add_spec].
  First, we state the lemma: *)
  Lemma doubled_ok : verify[module1] doubled_spec.
  (* [verify[ast.module] spec] will produce the correct statement. *)
  Proof.
    verify_spec.
    go.
    have ->: (n + 1 + (n - 1)) = 2 * n by lia.
    go.
    Arith.arith_simpl.
    remove_useless_trim.
  Qed.

End with_cpp.

(*
"verifying open programs" might be confusing.

_Maybe_ hide cpp.prog from the user.

Again, maybe keep the very first thing very easy.

Defer arithmetic hard.

- First tutorial should be very accessible.
- Second tutorial should be for our main target audience.

Topics for tutorial:
- very early "first verification"
- demonstrating argument specs and function calls
- demonstrating hints for Reps (like the hints we needed for frac splitting with Mansky, plus lazy unfold)
 *)
