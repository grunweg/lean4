/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE

  Author: Lev Nachmanson
*/


#include "util/lp/binary_heap_upair_queue.h"
namespace lean {
template <typename T> binary_heap_upair_queue<T>::binary_heap_upair_queue(unsigned size) : m_q(size), m_pairs(size) {
        lean_assert(size);
        for (unsigned i = 0; i < size; i++)
            m_available_spots.push_back(i);
}
template <typename T> unsigned
    binary_heap_upair_queue<T>::dequeue_available_spot() {
    lean_assert(m_available_spots.empty() == false);
    unsigned ret = m_available_spots.back();
    m_available_spots.pop_back();
    return ret;
}
template <typename T> void binary_heap_upair_queue<T>::remove(unsigned i, unsigned j) {
        upair p(i, j);
        auto it = m_pairs_to_index.find(p);
        if (it == m_pairs_to_index.end())
            return; // nothing to do
        m_q.remove(it->second);
        m_available_spots.push_back(it->second);
        m_pairs_to_index.erase(it);
    }


template <typename T> bool binary_heap_upair_queue<T>::ij_index_is_new(unsigned ij_index) const {
        for (auto it : m_pairs_to_index) {
            if (it.second == ij_index)
                return false;
        }
        return true;
    }

template <typename T> void binary_heap_upair_queue<T>::enqueue(unsigned i, unsigned j, const T & priority) {
        upair p(i, j);
        auto it = m_pairs_to_index.find(p);
        unsigned ij_index;
        if (it == m_pairs_to_index.end()) {
            // it is a new pair, let us find a spot for it
            if (m_available_spots.empty()) {
                // we ran out of empty spots
                unsigned size_was = m_pairs.size();
                unsigned new_size = size_was << 1;
                for (unsigned i = size_was; i < new_size; i++)
                    m_available_spots.push_back(i);
                m_pairs.resize(new_size);
            }
            ij_index = dequeue_available_spot();
            // lean_assert(ij_index<m_pairs.size() && ij_index_is_new(ij_index));
            m_pairs[ij_index] = p;
            m_pairs_to_index[p] = ij_index;
        } else {
            ij_index = it->second;
        }
        m_q.enqueue(ij_index, priority);
    }

template <typename T> void binary_heap_upair_queue<T>::dequeue(unsigned & i, unsigned &j) {
        lean_assert(!m_q.is_empty());
        unsigned ij_index = m_q.dequeue();
        upair & p = m_pairs[ij_index];
        i = p.first;
        j = p.second;
        m_available_spots.push_back(ij_index);
        m_pairs_to_index.erase(p);
    }


template <typename T> T binary_heap_upair_queue<T>::get_priority(unsigned i, unsigned j) const {
        auto it =  m_pairs_to_index.find(std::make_pair(i, j));
        if (it == m_pairs_to_index.end())
            return T(0xFFFFFF); // big number
        return m_q.get_priority(it->second);
    }

#ifdef LEAN_DEBUG
template <typename T> bool binary_heap_upair_queue<T>::pair_to_index_is_a_bijection() const {
        std::set<int> tmp;
        for (auto p : m_pairs_to_index) {
            unsigned j = p.second;
            auto it = tmp.find(j);
            if (it != tmp.end()) {
                std::cout << "for pair (" << p.first.first << ", " << p.first.second << "),  the index " << j
                          << " is already inside " << std::endl;
                lean_assert(false);
            } else {
                tmp.insert(j);
            }
        }
        return true;
    }

template <typename T> bool binary_heap_upair_queue<T>::available_spots_are_correct() const {
        std::set<int> tmp;
        for (auto p : m_available_spots){
            tmp.insert(p);
        }
        if (tmp.size() != m_available_spots.size())
            return false;
        for (auto it : m_pairs_to_index)
            if (tmp.find(it.second) != tmp.end())
                return false;
        return true;
    }
#endif
}
/*
  #include <unordered_set>
#include <queue>
#include <vector>
#include <set>
#include <utility>
typedef std::pair<unsigned, unsigned> upair;

namespace lean {
template <typename  T>
class binary_heap_upair_queue {
    binary_heap_priority_queue<T> m_q;
    std::unordered_map<upair, unsigned> m_pairs_to_index;
    std::vector<upair> m_pairs; // inverse to index
    std::vector<unsigned> m_available_spots;
public:
    binary_heap_upair_queue(unsigned size) : m_q(size), m_pairs(size) {
        lean_assert(size);
        for (unsigned i = 0; i < size; i++)
            m_available_spots.push_back(i);
    }

    unsigned dequeue_available_spot() {
        lean_assert(m_available_spots.empty() == false);
        unsigned ret = m_available_spots.back();
        m_available_spots.pop_back();
        return ret;
    }

    void remove(unsigned i, unsigned j) {
        upair p(i, j);
        auto it = m_pairs_to_index.find(p);
        if (it == m_pairs_to_index.end())
            return; // nothing to do
        m_q.remove(it->second);
        m_available_spots.push_back(it->second);
        m_pairs_to_index.erase(it);
    }


    bool ij_index_is_new(unsigned ij_index) const {
        for (auto it : m_pairs_to_index) {
            if (it.second == ij_index)
                return false;
        }
        return true;
    }

    void enqueue(unsigned i, unsigned j, const T & priority) {
        upair p(i, j);
        auto it = m_pairs_to_index.find(p);
        unsigned ij_index;
        if (it == m_pairs_to_index.end()) {
            // it is a new pair, let us find a spot for it
            if (m_available_spots.empty()) {
                // we ran out of empty spots
                unsigned size_was = m_pairs.size();
                unsigned new_size = size_was << 1;
                for (unsigned i = size_was; i < new_size; i++)
                    m_available_spots.push_back(i);
                m_pairs.resize(new_size);
            }
            ij_index = dequeue_available_spot();
            // lean_assert(ij_index<m_pairs.size() && ij_index_is_new(ij_index));
            m_pairs[ij_index] = p;
            m_pairs_to_index[p] = ij_index;
        } else {
            ij_index = it->second;
        }
        m_q.enqueue(ij_index, priority);
    }

    void dequeue(unsigned & i, unsigned &j) {
        lean_assert(!m_q.is_empty());
        unsigned ij_index = m_q.dequeue();
        upair & p = m_pairs[ij_index];
        i = p.first;
        j = p.second;
        m_available_spots.push_back(ij_index);
        m_pairs_to_index.erase(p);
    }

    bool is_empty() const {
        return m_q.is_empty();
    }

    unsigned size() const {
        return m_q.size();
    }

    bool contains(unsigned i, unsigned j) const {
        return m_pairs_to_index.find(std::make_pair(i, j)) != m_pairs_to_index.end();
    }

    T get_priority(unsigned i, unsigned j) const {
        auto it =  m_pairs_to_index.find(std::make_pair(i, j));
        if (it == m_pairs_to_index.end())
            return T(0xFFFFFF); // big number
        return m_q.get_priority(it->second);
    }

    bool pair_to_index_is_a_bijection() const {
        std::set<int> tmp;
        for (auto p : m_pairs_to_index) {
            unsigned j = p.second;
            auto it = tmp.find(j);
            if (it != tmp.end()) {
                std::cout << "for pair (" << p.first.first << ", " << p.first.second << "),  the index " << j
                          << " is already inside " << std::endl;
                lean_assert(false);
            } else {
                tmp.insert(j);
            }
        }
        return true;
    }

    bool available_spots_are_correct() const {
        std::set<int> tmp;
        for (auto p : m_available_spots){
            tmp.insert(p);
        }
        if (tmp.size() != m_available_spots.size())
            return false;
        for (auto it : m_pairs_to_index)
            if (tmp.find(it.second) != tmp.end())
                return false;
        return true;
    }

    bool is_correct() const {
        return m_q.is_consistent() && pair_to_index_is_a_bijection() && available_spots_are_correct();
    }
};
}
*/
