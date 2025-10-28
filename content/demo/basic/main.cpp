/*
 * Copyright (C) 2024-2025 SkyLabs AI.
 *
 * SPDX-License-Identifier:MIT-0
 */

int add(int x, int y)
{
  return x+y;
}


int doubled (int n)
{
  int a = n+1;
  int b = n-1;
  return a+b;
}


int quadruple (int n)
{
  int m = n + n;
  return m + m;
}


int abs (int x)
{
  if (x >= 0) {
    return x;
  }
  else {
    return -x;
  }
}

////// Pointers and Simple Ownership

int read (int *p)
{
  return *p;
}


int quadruple_mem (int *p)
{
  int m = *p + *p;
  return m + m;
}


int abs_mem (int *p)
{
  int x = *p;
  if (x >= 0) {
    return x;
  }
  else {
    return -x;
  }
}


//// Write Example

void incr (int *p)
{
  *p = *p+1;
}


void zero (int *p)
{
  *p = 0;
}


void inplace_double (int *p)
{
  int n = *p;
  int m = n + n;
  *p = m;
}



unsigned int add_mem (unsigned int *p, unsigned int *q)
{
  unsigned int m = *p;
  unsigned int n = *q;
  return m+n;
}


void swap (unsigned int *p, unsigned int *q)
{
  unsigned int m = *p;
  unsigned int n = *q;
  *p = n;
  *q = m;
}


void transfer (unsigned int *p, unsigned int *q)
{
  unsigned int n = *p;
  unsigned int m = *q;
  unsigned int s = n + m;
  *p = s;
  *q = 0;
}


////// Aggregates
struct point { int x; int y; };

void transpose (struct point *p)
{
  int temp_x = p->x;
  int temp_y = p->y;
  p->x = temp_y;
  p->y = temp_x;
}
