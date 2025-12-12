---
title: Inlining during verification
key: bluerock.auto.cpp.specs.inline
---
(*|
Use the class `ShouldInlineFunction` to mark a function as "inline during verification".

```coq
#[local] Instance foo_inline : ShouldInlineFunction "foo::foo()" := {}.
```

Note that inlining a function will repeat the proof of the function
in (potentially) many places and can therefore be very expensive. Clearly, you
should never mark a function inline unless it has a *completely* automatic proof.

These hints should *ALMOST ALWAYS* be local, and publically visible member functions
should *never* be marked inline.
EXCEPTIONS:
- trivial C++ wrappers might warrant inlining, especially if not used often.
  For instance, using `ShouldInlineFunction` for
  `T* operator->() const { return get_ptr(); }`
  is reasonable.
|*)
