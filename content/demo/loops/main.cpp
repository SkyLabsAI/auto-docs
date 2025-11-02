/*
 * Copyright (C) 2024-2025 SkyLabs AI.
 *
 * SPDX-License-Identifier:MIT-0
 */

int while_loop() {
  int i = 0;
  while (++i < 10) {}
  return i;
}

int while_decl_loop() {
  int i = 0;
  while (auto t = ++i < 10)
    (void)t;
  return i;

}

int do_while_loop() {
  int i = 0;
  do {
  } while (++i < 10);
  return i;
}

int for_loop() {
  for (int i = 0; i < 10; ++i) {
    if (i == 9) {
      return 10;
    }
  }
  return 0;
}
