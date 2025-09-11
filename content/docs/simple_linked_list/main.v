(*@HIDE@*)
Require Import bluerock.auto.cpp.prelude.proof.
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.
(*@END-HIDE@*)

(*|
<details class="alert alert-info">
<summary>A C++ implementation of a singly-linked list</summary>
|*)
cpp.prog source prog cpp:{{
  class linked_list;

  class ll_node {
    friend class linked_list;

  public:
    ll_node(unsigned int data): _data(data), _next(nullptr) {}
    ll_node(unsigned int data, ll_node* next): _data(data), _next(next) {}

    // getters
    unsigned int get_data();

    // setters
    void set_data(unsigned int data);

  private:
    unsigned int _data;
    ll_node* _next;
  };

  class linked_list {
  public:
    linked_list(ll_node* root): _root(root) {}

    // API
    unsigned int length() const;
    void reverse();
    void push (ll_node* node);
    ll_node* pop();
    void append(linked_list* l);
    void merge(linked_list* l);

  private:
    ll_node* _root;
  };

  // getters
  unsigned int
  ll_node::get_data() {
    return this->_data;
  }

  // setters
  void
  ll_node::set_data(unsigned int data) {
    this->_data = data;
  }

  // API
  unsigned int
  linked_list::length() const {
    unsigned int length = 0;
    ll_node* cur = this->_root;

    while (cur) {
      length++;
      cur = cur->_next;
    }

    return length;
  }

  void
  linked_list::reverse() {
    ll_node* cur = this->_root;
    ll_node* prev = nullptr;
    ll_node* next = nullptr;

    while (cur) {
      next = cur->_next;
      cur->_next = prev;
      prev = cur;
      cur = next;
    }

    this->_root = prev;
  }

  void
  linked_list::push (ll_node* node) {
    node->_next = this->_root;
    this->_root = node;
  }

  ll_node*
  linked_list::pop() {
    ll_node* result = this->_root;

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

    ll_node* cur = this->_root;
    for (; cur->_next; cur = cur->_next);

    cur->_next = l->_root;
    l->_root = nullptr;
  }

  void
  linked_list::merge(linked_list* l) {
    ll_node *merged = nullptr, **tail = &merged;

    ll_node *cur_l = l->_root;
    ll_node *cur_this = this->_root;
    l->_root = nullptr;

    while (cur_l && cur_this) {
      if (cur_l->_data < cur_this->_data) {
        *tail = cur_l;
        cur_l = cur_l->_next;
      } else {
        *tail = cur_this;
        cur_this = cur_this->_next;
      }
      tail = &(( *tail)->_next);
    }

    *tail = cur_this ? cur_this : cur_l;
    this->_root = merged;
  }
}}.
(*|
</details>

## Representation Predicates for the Node and the List
|*)
NES.Begin linked_list.
Section reps.
  Context `{Σ : cpp_logic} `{MOD: source ⊧ σ}.

  Definition nodeR (q : cQp.t) (data : N) (next : ptr) : Rep :=
    _field "ll_node::_data" |-> uintR q data **
    _field "ll_node::_next" |-> ptrR<"ll_node"> q next **
    structR "ll_node" q.

  Fixpoint nodesR (q : cQp.t) (ls : list N) : Rep :=
    match ls with
    | [] => nullR
    | data :: ls' =>
      ∃ next : ptr, nodeR q data next ** pureR (next |-> nodesR q ls')
    end.

  Definition R (q : cQp.t) (ls : list N) : Rep :=
    ∃ root : ptr,
    _field "linked_list::_root" |-> ptrR<"ll_node"> q root **
    structR "linked_list" q **
    pureR (root |-> nodesR q ls).
End reps.
#[global] Hint Opaque nodeR nodesR R : br_opacity typeclass_instances.

(*|
## Specifying and Verifying Node
|*)
NES.Begin node.

(*|### Specifications |*)
  cpp.spec "ll_node::ll_node(unsigned int)" from source as ctor_null_spec with (
    \this this
    \arg{data} "data" (Vn data)
    \post this |-> nodeR 1$m data nullptr
  ).

  cpp.spec "ll_node::ll_node(unsigned int, ll_node* )" from source
      as ctor_next_spec with (
    \this this
    \arg{data} "data" (Vn data)
    \arg{next} "next" (Vptr next)
    \post this |-> nodeR 1$m data next
  ).

  cpp.spec "ll_node::get_data()" from source as get_data_spec with (
    \this this
    \prepost{q data next} this |-> nodeR q$c data next
    \post[Vn data] emp
  ).

  cpp.spec "ll_node::set_data(unsigned int)" from source as set_data_spec with (
    \this this
    \arg{data} "data" (Vn data)
    \pre{data_old next} this |-> nodeR 1$m data_old next
    \post this |-> nodeR 1$m data next
  ).

(*|### Proofs|*)
  NES.Begin proof.
  (*| #### Verifying Constructors |*)
  Set Default Proof Using "Type*".
  Section proofs.
    Context `{Σ : cpp_logic} `{MOD: source ⊧ σ}.

    Lemma ctor_null_ok : verify[source] ctor_null_spec.
    Proof. verify_spec. go. rewrite /nodeR. work. Qed.

    Lemma ctor_next_ok : verify[source] ctor_next_spec.
    Proof. verify_spec. go. rewrite /nodeR. work. Qed.
  End proofs.

  (*| #### Veryfing Methods |*)
  #[only(lazy_unfold)] derive nodeR.
  Section proofs.
    Context `{Σ : cpp_logic} `{MOD: source ⊧ σ}.

    Lemma get_data_ok : verify[source] get_data_spec.
    Proof. verify_spec. go. Qed.

    Lemma set_data_ok : verify[source] set_data_spec.
    Proof. verify_spec. go. Qed.
  End proofs.
  NES.End proof.
NES.End node.

(*|
## Specifying and Verifying List
|*)
cpp.spec "linked_list::linked_list(ll_node* )" from source as ctor_spec with (
  \this this
  \arg{root} "root" (Vptr root)
  \pre{ls : list N} root |-> nodesR 1$m ls
  \post this |-> R 1$m ls
).

Section proofs.
  Context `{Σ : cpp_logic} `{MOD: source ⊧ σ}.
  Set Default Proof Using "MOD".

(*| ## Verifying Constructors |*)
  Lemma ctor_ok : verify[source] ctor_spec.
  Proof. verify_spec. go. rewrite /R. work. Qed.

End proofs.
NES.End linked_list.
