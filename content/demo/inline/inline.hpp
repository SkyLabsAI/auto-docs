/*
 * Copyright (C) 2022 SkyLabs AI.
 *
 * SPDX-License-Identifier:MIT-0
 */

struct C {
  int inline_O() { return 0; }
  int& inline_L(int& x) { return x; }
  int&& inline_X(int& x) { return static_cast<int&&>(x); }
  C inline_I() { return C(); }
};

int inline_O() { return 0; }
int& inline_L(int& x) { return x; }
int&& inline_X(int& x) { return static_cast<int&&>(x); }
C inline_I() { return C(); }

void into_L(int&) {}
void into_X(int&&) {}

void test(C* p) {
  int x{0};

  inline_O();
  inline_L(x);
  inline_X(x);
  inline_I();

  C c;
  c.inline_O();
  c.inline_L(x);
  c.inline_X(x);
  c.inline_I();

  into_L(inline_L(x));
  into_X(inline_X(x));

  // TODO currently unsupported
  //p->~C();
}
