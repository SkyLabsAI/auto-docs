/**
 * Copyright (C) 2025 SkyLabs AI.
 * All rights reserved.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BlueRock Exception for use over network, see repository root for details.
 */

class linked_list;

class node {
  friend class linked_list;

public:
  node(unsigned int data): _data(data), _next(nullptr) {}
  node(unsigned int data, node* next): _data(data), _next(next) {}

  // getters
  unsigned int get_data();

  // setters
  void set_data(unsigned int data);

private:
  unsigned int _data;
  node* _next;
};

class linked_list {
public:
  linked_list(node* root): _root(root) {}

  // API
  unsigned int length() const;
  void reverse();
  void push (node* node);
  node* pop();
  void append(linked_list* l);
  void merge(linked_list* l);

private:
  node* _root;
};
