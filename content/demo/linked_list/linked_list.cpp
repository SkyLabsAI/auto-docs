/**
 * Copyright (C) 2025 SkyLabs AI.
 * All rights reserved.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BlueRock Exception for use over network, see repository root for details.
 */

#include "linked_list.hpp"

// getters
unsigned int
node::get_data() {
  return this->_data;
}

// setters
void
node::set_data(unsigned int data) {
  this->_data = data;
}

// API
unsigned int
linked_list::length() const {
  unsigned int length = 0;
  node* cur = this->_root;

  while (cur) {
    length++;
    cur = cur->_next;
  }

  return length;
}

void
linked_list::reverse() {
  node* cur = this->_root;
  node* prev = nullptr;
  node* next = nullptr;

  while (cur) {
    next = cur->_next;
    cur->_next = prev;
    prev = cur;
    cur = next;
  }

  this->_root = prev;
}

void
linked_list::push (node* node) {
  node->_next = this->_root;
  this->_root = node;
}

node*
linked_list::pop() {
  node* result = this->_root;

  if (result) {
    this->_root = result->_next;
    result->_next = nullptr;
  }

  return result;
}

void
linked_list::append(linked_list* l) {
  if (!this->_root) {
    this->_root = l->_root;
    l->_root = nullptr;
    return;
  }

  node* cur = this->_root;
  for (; cur->_next; cur = cur->_next);

  cur->_next = l->_root;
  l->_root = nullptr;
}

void
linked_list::merge(linked_list* l) {
  node *merged = nullptr, **tail = &merged;

  node *cur_l = l->_root;
  node *cur_this = this->_root;
  l->_root = nullptr;

  while (cur_l && cur_this) {
    if (cur_l->_data < cur_this->_data) {
      *tail = cur_l;
      cur_l = cur_l->_next;
    } else {
      *tail = cur_this;
      cur_this = cur_this->_next;
    }
    tail = &((*tail)->_next);
  }

  *tail = cur_this ? cur_this : cur_l;
  this->_root = merged;
}
