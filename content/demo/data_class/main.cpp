/*
 * Copyright (C) 2025 SkyLabs AI.
 *
 * SPDX-License-Identifier:MIT-0
 */

struct two_ints {
  int x{0};
  int y{0};
};

two_ints add(const two_ints &a, const two_ints &b) {
  return {a.x + b.x, a.y + b.y};
}

void test() {
  two_ints a{1,2};
  two_ints b{3,4};
  add(a, b);
}
