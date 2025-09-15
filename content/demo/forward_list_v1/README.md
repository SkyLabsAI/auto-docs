---
title: Forward List
eleventyNavigation:
  key: demo-forward_list_v1
  parent: demo
---

# `forward_list`

This directory demonstrates a technique to specifying `forward_list<int>` iterators
that is sufficient for simple uses of iterators. The technique approximates the
exact position of the iterator in the list using a boolean to distinguish the end
iterator from iterators that are not the end.

The specification under-approximates the full behavior of iterators in several ways.
1. The model of the iterator only tracks whether the iterator is at the end or
   not. This is sufficient for discharging the obligation that you can not
   de-reference an end iterator, but it does not allow you to maintain a precise
   pointer into the list, so specs are under-constrained when you access the element.
2. Creating an iterator on a list consumes a fraction of the underlying list.
   This prevents concurrent modifications, but is more restrictive than necessary
   especially in the context of mutable iterators.

More powerful specifications that relax these restrictions require more
sophisticated specifications that separate the ownership of the list spine from
the list contents. These will be provided by the specifications of the standard
library.
