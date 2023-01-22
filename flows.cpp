#include <bits/stdc++.h>

template <typename T>
class FlowGraph {
public:
  class Edge {
  public:
    Edge() = default;

    Edge(int from, int to, T cap)
        : from_(from),
          to_(to),
          capacity_(cap) {
    }

    [[nodiscard]]
    inline int GetFrom() const {
      return from_;
    }

    [[nodiscard]]
    inline int GetTo() const {
      return to_;
    }

    [[nodiscard]]
    inline T GetFlow() const {
      return flow_;
    }

    [[nodiscard]]
    inline T GetCapacity() const {
      return capacity_;
    }

    [[nodiscard]]
    inline T GetPotential() const {
      return capacity_ - flow_;
    }

    inline void AddFlow(const T& increment) {
      flow_ += increment;
    }

  private:
    int from_{};
    int to_{};
    T flow_{};
    T capacity_;
  };

  FlowGraph(int start,
            int terminal,
            int vertices,
            int edges = -1)
      : start_(start),
        terminal_(terminal),
        n_(vertices),
        adj_(vertices),
        distance_(vertices),
        first_alive_edge_(vertices) {
    if (edges != -1) {
      edges_.reserve(edges * 2);
    }
  }

  inline int AddDirectedEdge(int from, int to, T cap) {
    edges_.emplace_back(from, to, cap);
    adj_[from].emplace_back(ssize(edges_) - 1);
    edges_.emplace_back(to, from, 0);
    adj_[to].emplace_back(ssize(edges_) - 1);
    return adj_[from].back();
  }

  inline int AddBidirectionalEdge(int from, int to, T cap) {
    edges_.emplace_back(from, to, cap);
    adj_[from].emplace_back(ssize(edges_) - 1);
    edges_.emplace_back(to, from, cap);
    adj_[to].emplace_back(ssize(edges_) - 1);
    return adj_[from].back();
  }

  [[nodiscard]]
  inline const Edge& GetEdge(int id) {
    return edges_[id];
  }

  /* Computes maximal flow in O(V^2 * E) */
  T Dinic() {
    T augment;
    T max_flow = 0;

    while (Bfs()) {
      while ((augment = Dfs(start_, std::numeric_limits <T>::max())) > 0) {
        max_flow += augment;
      }
    }

    return max_flow;
  }

  /* Computes maximal flow in O(VE * log(C)), where C is the maximal single edge capacity in the network*/
  T ScalingDinic() {
    T max_capacity = 0;
    for (const Edge& e : edges_) {
      max_capacity = std::max(max_capacity, e.GetCapacity());
    }

    while (lower_bound_ * 2 <= max_capacity) {
      lower_bound_ *= 2;
    }

    T max_flow = 0;
    while (lower_bound_ > 0) {
      max_flow += Dinic();
      lower_bound_ /= 2;
    }

    return max_flow;
  }

  /* O(E)
   * Yields edges which are present in minimal cut between start and terminal and size of minimal cut
   * Make sure you've called Dinic() before calling this */
  std::pair <std::vector <Edge>, T> MinCut() {
    std::vector <char> reachable(n_);

    auto Dfs = [&](const auto& Self, int node) -> void {
      reachable[node] = true;
      for (const int& id : adj_[node]) {
        Edge& e = edges_[id];
        if (!reachable[e.GetTo()]
            && e.GetPotential() > 0) {
          Self(Self, e.GetTo());
        }
      }
    };

    Dfs(Dfs, start_);
    T min_cut_size = 0;
    std::vector <Edge> answer;
    for (int i = 0; i < ssize(edges_) / 2; ++i) {
      if (reachable[edges_[i * 2].GetTo()] ^ reachable[edges_[i * 2 + 1].GetTo()]) {
        if (reachable[edges_[i * 2].GetTo()]) {
          answer.push_back(edges_[i * 2 + 1]);
        } else {
          answer.push_back(edges_[i * 2]);
        }
        min_cut_size += std::max(edges_[i * 2].GetFlow(), edges_[i * 2 + 1].GetFlow());
      }
    }

    return {answer, min_cut_size};
  }

  /* Decomposes the found flow to paths. Runs in O(VE)*/
  std::vector <std::pair <std::vector <int>, T>> FlowDecomposition() {
    std::vector <int> path;
    std::vector <std::pair <std::vector <int>, T>> decomposition;
    std::fill(begin(first_alive_edge_), end(first_alive_edge_), 0);

    int timer = 0;
    std::vector <int> used(n_, -1);

    auto Dfs = [&](const auto& Self, int node, T path_min) -> T {
      if (node == terminal_) {
        path.emplace_back(node);
        return path_min;
      }
      
      if (used[node] == timer) {
        return path_min;
      }

      int id;
      T flow_found;
      used[node] = timer;
      int& start = first_alive_edge_[node];
      
      for (int i = start; i < ssize(adj_[node]); ++i) {
        id = adj_[node][i];
        Edge& e = edges_[id];
        if (e.GetFlow() > 0) {
          flow_found = Self(Self, e.GetTo(), std::min(path_min, e.GetFlow()));
          if (flow_found > 0) {
            path.emplace_back(node);
            e.AddFlow(-flow_found);
            BackEdge(id).AddFlow(flow_found);
            if (e.GetFlow() == 0) {
              start += 1;
            }
            return flow_found;
          } else {
            start += 1;
          }
        }
      }

      return 0;
    };

    T found;
    while ((found = Dfs(Dfs, start_, std::numeric_limits <T>::max())) > 0) {
      timer += 1;
      std::reverse(begin(path), end(path));
      decomposition.emplace_back(path, found);
      path.clear();
    }

    return decomposition;
  }

private:
  [[nodiscard]]
  inline Edge& BackEdge(int id) {
    return edges_[id ^ 1];
  }

  bool Bfs() {
    std::fill(begin(distance_), end(distance_), -1);

    distance_[start_] = 0;
    auxiliary_queue_.push(start_);
    while (!auxiliary_queue_.empty()) {
      int node = auxiliary_queue_.front();
      auxiliary_queue_.pop();
      for (const int& id : adj_[node]) {
        Edge& e = edges_[id];
        if (distance_[e.GetTo()] == -1
            && lower_bound_ <= e.GetPotential()) {
          distance_[e.GetTo()] = distance_[node] + 1;
          auxiliary_queue_.push(e.GetTo());
        }
      }
    }

    if (distance_[terminal_] == -1) {
      return false;
    }
    std::fill(begin(first_alive_edge_), end(first_alive_edge_), 0);
    return true;
  }

  T Dfs(int node, T augment) {
    if (node == terminal_) {
      return augment;
    }

    int id;
    T pushed;
    int& start = first_alive_edge_[node];

    for (int i = start; i < ssize(adj_[node]); ++i) {
      id = adj_[node][i];
      Edge& e = edges_[id];

      if (distance_[node] + 1 != distance_[e.GetTo()]
          || e.GetPotential() < lower_bound_) {
        start += 1;
        continue;
      }

      pushed = Dfs(e.GetTo(), std::min(augment, e.GetPotential()));
      if (pushed > 0) {
        e.AddFlow(pushed);
        BackEdge(id).AddFlow(-pushed);
        if (e.GetPotential() < lower_bound_) {
          start += 1;
        }
        return pushed;
      } else {
        start += 1;
      }
    }

    return 0;
  }

  const int start_;
  const int terminal_;

  T lower_bound_ = 1;

  int n_;
  std::vector <Edge> edges_;
  std::vector <int> distance_;
  std::queue <int> auxiliary_queue_;
  std::vector <int> first_alive_edge_;
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
