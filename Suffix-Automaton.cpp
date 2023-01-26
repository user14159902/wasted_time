#include <bits/stdc++.h>

template <const int sigma,
    const int char_offset>
class SuffixAutomaton {
public:
  class Node {
  public:
    Node()
        : parent_(-1),
          suffix_link_(-1) {
      memset(&next_, -1, sigma * sizeof(int));
    }

    explicit Node(int parent)
        : parent_(parent),
          suffix_link_(-1) {
      memset(&next_, -1, sigma * sizeof(int));
    }

    int parent_;
    int suffix_link_;
    int length_{};
    int occurrences_{};
    std::array <int, sigma> next_{};

    bool is_terminal_{};
  };

  [[nodiscard]]
  std::optional <Node> GetNode(size_t id) const {
    if (id <= nodes_count_) {
      return aut_[id];
    }
    return std::nullopt;
  }

  explicit SuffixAutomaton(const std::string::const_iterator& first,
                           const std::string::const_iterator& last) {
    aut_.reserve(std::distance(first, last) * 2);
    aut_.emplace_back();

    int last_state = 0;
    for (auto it = first; it != last; ++it) {
      last_state = Extend(last_state, *it - char_offset);
    }

    while (last_state > 0) {
      aut_[last_state].occurrences_ = 1;
      aut_[last_state].is_terminal_ = true;
      last_state = aut_[last_state].suffix_link_;
    }

    TopologicalSort();
    for (int i = nodes_count_ - 1; i >= 0; --i) {
      const int& node = sorted_order_[i];
      for (const int& to : aut_[node].next_) {
        if (to != -1) {
          aut_[node].occurrences_ += aut_[to].occurrences_;
        }
      }
    }
  }

  int GetOccurrences(const std::string::const_iterator& first,
                     const std::string::const_iterator& last) {
    int state = 0;
    for (auto it = first; it != last; ++it) {
      if (aut_[state].next_[*it - char_offset] == -1) {
        return 0;
      }
      state = aut_[state].next_[*it - char_offset];
    }
    return aut_[state].occurrences_;
  }

private:
  void TopologicalSort() {
    std::vector <int> deque;
    /* reserve for efficiency
     * also, it helps to avoid iterator invalidation after push_backs */
    deque.reserve(nodes_count_ + 1);
    sorted_order_.reserve(nodes_count_ + 1);
    std::vector <int> in_degree(nodes_count_ + 1);

    for (int i = 0; i <= nodes_count_; ++i) {
      for (const int& to : aut_[i].next_) {
        if (to != -1) {
          in_degree[to] += 1;
        }
      }
    }

    for (int i = 0; i <= nodes_count_; ++i) {
      if (in_degree[i] == 0) {
        deque.push_back(i);
      }
    }

    auto deque_it = begin(deque);
    while (deque_it != deque.end()) {
      int node = *deque_it;
      std::advance(deque_it, 1);
      sorted_order_.push_back(node);
      for (const int& to : aut_[node].next_) {
        if (to != -1 && --in_degree[to] == 0) {
          deque.push_back(to);
        }
      }
    }

    if (size(sorted_order_) != nodes_count_ + 1) {
      throw std::logic_error("Wrong automaton construction");
    }
  }

  int Clone(int parent, const int& current_transition, const int& c) {
    aut_.push_back(aut_[current_transition]);
    aut_.back().parent_ = parent;
    aut_.back().length_ = aut_[parent].length_ + 1;
    
    int clone = ++nodes_count_;
    aut_[current_transition].suffix_link_ = clone;
    while (parent != -1 && aut_[parent].next_[c] == current_transition) {
      aut_[parent].next_[c] = clone;
      parent = aut_[parent].suffix_link_;
    }

    return clone;
  }

  int Choose(int node, const int& c) {
    int q = aut_[node].next_[c];
    if (aut_[q].parent_ == node) {
      return q;
    } else {
      return Clone(node, q, c);
    }
  }

  int Extend(int last_state, const int& c) {
    if (aut_[last_state].next_[c] != -1) {
      return Choose(last_state, c);
    }

    int new_state = ++nodes_count_;
    aut_.emplace_back(last_state);
    aut_[new_state].length_ = aut_[last_state].length_ + 1;

    while (last_state != -1 && aut_[last_state].next_[c] == -1) {
      aut_[last_state].next_[c] = new_state;
      last_state = aut_[last_state].suffix_link_;
    }

    if (last_state != -1) {
      aut_[new_state].suffix_link_ = Choose(last_state, c);
    } else {
      aut_[new_state].suffix_link_ = 0;
    }
    return new_state;
  }

  int nodes_count_{};
  std::vector <Node> aut_;
  std::vector <int> sorted_order_;
};

void RunCase() {
  int n;
  std::cin >> n;

  std::vector <std::string> words(n);
  for (auto& word : words) {
    std::cin >> word;
  }

  std::string text;
  std::cin >> text;
  SuffixAutomaton <26, 97> automaton(begin(text), end(text));

  for (const auto& word : words) {
    std::cout << automaton.GetOccurrences(begin(word), end(word)) << "\n";
  }
}

int main() {
  std::ios_base::sync_with_stdio(false);
  std::cin.tie(nullptr);
  int tt = 1;
  //std::cin >> tt;
  while (tt--) {
    RunCase();
  }
  return 0;
}
