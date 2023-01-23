#include <bits/stdc++.h>

class Matching {
public:
  Matching(int left,
           int right)
      : adj_(left),
        distances_(left),
        left_(left),
        right_(right),
        match_left_(left, -1),
        match_right_(right, -1) {
  }

  inline void AddEdge(int from, int to) {
    adj_[from].emplace_back(to);
  }

  /* O(E * sqrt(V)*/
  int HopcroftKarp() {
    int matching = 0;
    int augment = 1;

    while (augment > 0) {
      Bfs();
      augment = 0;
      for (int i = 0; i < left_; ++i) {
        if (match_left_[i] == -1) {
          augment += Dfs(i);
        }
      }
      matching += augment;
    }

    return matching;
  }

  std::vector <std::pair <int, int>> GetMatching() {
    std::vector <std::pair <int, int>> result;
    result.reserve(HopcroftKarp());

    for (int i = 0; i < left_; ++i) {
      if (match_left_[i] != -1) {
        result.emplace_back(i, match_left_[i]);
      }
    }

    return result;
  }

private:
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
    for (int i = 0; i < left_; ++i) {
      if (match_left_[i] == -1) {
        distances_[i] = 0;
        auxiliary_queue_.push(i);
      } else {
        distances_[i] = -1;
      }
    }

    while (!auxiliary_queue_.empty()) {
      int node = auxiliary_queue_.front();
      auxiliary_queue_.pop();
      for (const int& to : adj_[node]) {
        if (match_right_[to] != -1
            && distances_[match_right_[to]] == -1) {
          auxiliary_queue_.push(match_right_[to]);
          distances_[match_right_[to]] = distances_[node] + 1;
        }
      }
    }
  }

  int left_;
  int right_;
  std::vector <int> distances_;
  std::vector <int> match_left_;
  std::vector <int> match_right_;
  std::queue <int> auxiliary_queue_;
  std::vector <std::vector <int>> adj_;
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
