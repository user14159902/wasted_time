#include <bits/stdc++.h>

class Matching {
public:
  int left_fraction_;
  int right_fraction_;
  std::queue <int> aux_queue_;
  std::vector <int> distances_;
  std::vector <int> match_left_;
  std::vector <int> match_right_;
  std::vector <std::vector <int>> adj_;

  Matching(int left_fraction,
           int right_fraction)
  : adj_(left_fraction),
    distances_(left_fraction),
    left_fraction_(left_fraction),
    right_fraction_(right_fraction),
    match_left_(left_fraction, -1),
    match_right_(right_fraction, -1) {
  }

  void AddEdge(int from, int to) {
    adj_[from].emplace_back(to);
  }

  bool Dfs(int node) {
    for (const int& to : adj_[node]) {
      if (match_right_[to] == -1) {
        match_left_[node] = to;
        match_right_[to] = node;
        return true;
      }
    }

    for (const int& to : adj_[node]) {
      if (distances_[match_right_[to]] == distances_[node] + 1
      && Dfs(match_right_[to])) {
        match_left_[node] = to;
        match_right_[to] = node;
        return true;
      }
    }

    return false;
  }

   void Bfs() {
    for (int i = 0; i < left_fraction_; ++i) {
      if (match_left_[i] == -1) {
        distances_[i] = 0;
        aux_queue_.push(i);
      } else {
        distances_[i] = -1;
      }
    }

    while (!aux_queue_.empty()) {
      int node = aux_queue_.front();
      aux_queue_.pop();
      for (const int& to : adj_[node]) {
        if (match_right_[to] != -1
        && distances_[match_right_[to]] == -1) {
          aux_queue_.push(match_right_[to]);
          distances_[match_right_[to]] = distances_[node] + 1;
        }
      }
    }
  }

  int HopcroftKarp() {
    int matching = 0;
    int augment = 1;

    while (augment > 0) {
      Bfs();
      augment = 0;
      for (int i = 0; i < left_fraction_; ++i) {
        if (match_left_[i] == -1) {
          augment += Dfs(i);
        }
      }
      matching += augment;
    }

    return matching;
  }

  std::vector <std::pair <int, int>> GetEdges() {
    std::vector <std::pair <int, int>> result;
    result.reserve(HopcroftKarp());

    for (int i = 0; i < left_fraction_; ++i) {
      if (match_left_[i] != -1) {
        result.emplace_back(i, match_left_[i]);
      }
    }

    return result;
  }
};

void RunCase() {

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
