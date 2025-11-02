/**
 * Copyright (C) 2025 SkyLabs AI.
 * All rights reserved.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BlueRock Exception for use over network, see repository root for details.
 */

#include <cassert>
#include <list>
#include <forward_list>

using namespace std;

void
test(bool b) {
    assert(b);
}

// Basic test for <forward_list> and about <list>.
template <template<typename, typename> typename Container>
void
TestBasic() {
    Container<int, std::allocator<int>> v;
    v.push_front(3);
    v.push_front(2);
    v.push_front(1);
    test(v.front() == 1);
    v.pop_front();
    test(v.front() == 2);
    v.pop_front();
    test(v.front() == 3);
    v.pop_front();
    test(v.empty());
}

// A test about <list> instead of <forward_list>
// TODO: add proofs about this code.
void
TestList() {
    list<int> v;
    v.push_back(1);
    v.push_back(2);
    v.push_back(3);
    test(v.size() == 3);
}

template <template<typename, typename> typename Container>
unsigned int
TestIterators() {
    Container<int, std::allocator<int>> v;
    v.push_front(3);
    v.push_front(2);
    v.push_front(1);

    unsigned int acc = 0;
    for (int i : v) {
        acc += i;
    }
    return acc;
}

int
main() {
    TestBasic<std::forward_list>();
    TestBasic<std::list>();
    TestIterators<std::forward_list>();
    TestList();
    return 0;
}

