---
title: The `cpp.spec` command
key: bluerock.auto.elpi.cpp_spec
---
(*|
## Usage
```coq
#[ignore_errors, ignore_missing, convertible, verbose, debug]
cpp.spec <matcher> [as <spec-name>] [from <translation-unit>]
  [template <template-translation-unit>]
  [with (<spec>) | inline | default | (<constrained-spec>)].
```
where
```coq
  <matcher> ::= "f(int)" | (name "x") | ...
  <spec-name> ::= f_spec
  <translation-unit> ::= file_hpp.source | (file_hpp.source)
  <template-translation-unit> ::=
       file_hpp_templates.source | (file_hpp_templates.source)
  <spec> ::= <WPP-style-spec> | \this this <WPP-style-spec>
  <constrained-spec> ::= \requires .. \with <spec>
```

Without `from`, `cpp.spec` requires a section variable or `Let`
bindings of type `genv` (call it `σ`) and `TU ⊧ σ`.

<inline> and <default> are not yet supported for template
specifications.

### Attributes:
- `ignore_errors`	do not validate `\arg`ument types

- `convertible` find a symbol that is "convertible" to this  one, e.g.
    `D::foo()` is convertible to `C::foo()` if `D` extends `C`.
    This can be useful when base classes provide methods, but the base
    classes are implementation details, e.g. in the case of `std::atomic`
    and `std::atomic_base`.
    When using this feature, the specification should be written according
    to the written type, e.g. write the spec in terms of `C::foo()`
    rather than `D::foo()`.
    NOTE: Does not yet support template specifications.

- `ignore_missing` rather than failing when a function is not
    found, generate a trivial specification. This can be useful
    when trying to support multiple versions of a library.
    NOTE: Does not yet support template specifications.

- `verbose` verbose printing.
- `debug` debugging.

## Examples
```coq
cpp.spec "h(int, bool)" as "h_spec4" with (
  \arg{x} "x" (Vn x) (* Vn and int are compatible *)
  \arg{b} "b" (Vbool b)
  \post emp
).

Definition h_spec_gr : WpSpec_cpp := (
  \arg{x} "x" (Vint x)
  \arg{b} "b" (Vbool b)
  \post emp
).
cpp.spec "h(int, bool)" as "h_spec5" with (h_spec_gr).

(* wrong types *)
Definition h_spec_gr2 : WpSpec_cpp := (
  \arg{x} "x" (Vbool x)
  \arg{b} "b" (Vbool b)
  \post emp
).
Fail cpp.spec "h(int, bool)" as "h_spec6" with (h_spec_gr2).

cpp.spec "C::f()" with (
  \this this
  \pre emp
  \post emp
).
```
|*)
