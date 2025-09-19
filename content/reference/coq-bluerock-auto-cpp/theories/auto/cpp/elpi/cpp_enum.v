---
title: The `cpp.enum` command
key: bluerock.auto.elpi.cpp_enum
---
(*|
## Usage
```coq
#[disable(inj)]	(* do not synthesize `Inj eq eq to_val`, etc *)
#[verbose, debug]
cpp.enum "name" from <translation-unit> <kind>.
```
where
```coq
  <translation_unit> ::= <translation-unit-name> | (<translation-unit-expr>)
  <kind> ::= variant (* one of several, e.g. `enum YesNo { Yes | No };` *)
           | alias   (* an alias of a type, e.g. `enum align_t : size_t {};` *)
           | newtype (* same as alias, but introduces a new type *)
```
## Examples
We consider the following C++ code
```cpp
// test.cpp
namespace ns {
  enum E {
    X , Y
  };
}

enum ALIAS_int : int {};

enum NEW_TYPE_char : char {};
```
The command
```coq
Module ns.
  cpp.enum "ns::E" from (test_cpp.source) variant.
End ns.

```
generates in `Module ns`, among many things,
- the `E.t` type where `Variant t := X | Y.` (i.e. constructors `E.X` and `E.Y`)
- functions that convert `E.t` to `Z` and `N` (e.g. `E.to_Z`) and their injectivity properties
- `EqDecision` and `Finite` instances of `E.t`

The command
```coq
cpp.enum "ALIAS_int" from test_cpp.source alias.
```
generates facts that values of `ALIAS_int` are convertible with the C++ type `int`
(i.e. they also have the model as `Z`).

The command
```coq
cpp.enum "NEW_TYPE_char" from test_cpp.source newtype.
```
generates the new type `NEW_TYPE_char.t` that is convertible with the C++ type `char`
(i.e. it also has the model as `Z`).
|*)
