#include <bits/stdc++.h>

/* Max Flow in O(V^2E) or O(EV * log(max_capacity))*/
template <typename FlowType>
class FlowGraph {
public:
  class Edge {
  public:
    Edge() = default;

    Edge(int from, int to, FlowType cap)
        : from_(from),
          to_(to),
          capacity_(cap) {
    }

    [[nodiscard]]
    inline FlowType GetPotential() const {
      return capacity_ - flow_;
    }

    int from_;
    int to_;
    FlowType flow_{};
    FlowType capacity_;
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

  inline int AddDirectedEdge(int from, int to, FlowType cap) {
    edges_.emplace_back(from, to, cap);
    adj_[from].emplace_back(ssize(edges_) - 1);
    edges_.emplace_back(to, from, 0);
    adj_[to].emplace_back(ssize(edges_) - 1);
    return adj_[from].back();
  }

  inline int AddBidirectionalEdge(int from, int to, FlowType cap) {
    edges_.emplace_back(from, to, cap);
    adj_[from].emplace_back(ssize(edges_) - 1);
    edges_.emplace_back(to, from, cap);
    adj_[to].emplace_back(ssize(edges_) - 1);
    return adj_[from].back();
  }

  [[nodiscard]]
  inline std::optional <Edge> GetEdge(size_t id) {
    if (id < size(edges_)) {
      return edges_[id];
    } else {
      return std::nullopt;
    }
  }

  /* Computes maximal flow in O(V^2 * E) */
  FlowType Dinic() {
    FlowType augment;
    FlowType max_flow = 0;

    while (Bfs()) {
      while ((augment = Dfs(start_, std::numeric_limits <FlowType>::max())) > 0) {
        max_flow += augment;
      }
    }

    return max_flow;
  }

  /* Computes maximal flow in O(VE * log(C)), where C is the maximal single edge capacity in the network*/
  FlowType ScalingDinic() {
    FlowType max_capacity = 0;
    for (const Edge& e : edges_) {
      max_capacity = std::max(max_capacity, e.GetCapacity());
    }

    while (lower_bound_ * 2 <= max_capacity) {
      lower_bound_ *= 2;
    }

    FlowType max_flow = 0;
    while (lower_bound_ > 0) {
      max_flow += Dinic();
      lower_bound_ /= 2;
    }

    return max_flow;
  }

  /* O(E)
   * Yields edges which are present in minimal cut between start and terminal and size of minimal cut
   * Make sure you've called Dinic() before calling this */
  std::pair <std::vector <Edge>, FlowType> MinCut() {
    std::vector <char> reachable(n_);

    auto Dfs = [&](const auto& Self, int node) -> void {
      reachable[node] = true;
      for (const int& id : adj_[node]) {
        Edge& e = edges_[id];
        if (!reachable[e.to_] && e.GetPotential() > 0) {
          Self(Self, e.to_);
        }
      }
    };

    Dfs(Dfs, start_);
    FlowType min_cut_size = 0;
    std::vector <Edge> answer;

    for (int i = 0; i < ssize(edges_) / 2; ++i) {
      if (reachable[edges_[i * 2].to_] ^ reachable[edges_[i * 2 + 1].to_]) {
        if (reachable[edges_[i * 2].to_]) {
          answer.push_back(edges_[i * 2 + 1]);
        } else {
          answer.push_back(edges_[i * 2]);
        }
        min_cut_size += std::max(edges_[i * 2].flow_, edges_[i * 2 + 1].flow_);
      }
    }

    return {answer, min_cut_size};
  }

  /* Decomposes the found flow to paths. Runs in O(VE) */
  std::vector <std::pair <std::vector <int>, FlowType>> FlowDecomposition() {
    std::vector <int> path;
    std::vector <std::pair <std::vector <int>, FlowType>> decomposition;

    int timer = 0;
    std::vector <int> used(n_, -1);
    std::fill(begin(first_alive_edge_), end(first_alive_edge_), 0);

    auto Dfs = [&](const auto& Self, int node, FlowType path_min) -> FlowType {
      if (node == terminal_) {
        path.emplace_back(node);
        return path_min;
      }

      if (used[node] == timer) {
        return path_min;
      }

      int id;
      FlowType taken;
      used[node] = timer;
      int& start = first_alive_edge_[node];

      for (int i = start; i < ssize(adj_[node]); ++i) {
        id = adj_[node][i];
        Edge& e = edges_[id];
        Edge& e_rev = edges_[id ^ 1];
        if (e.flow_ > 0 && (taken = Self(Self, e.to_, std::min(path_min, e.flow_))) > 0) {
          path.emplace_back(node);
          e.flow_ -= taken;
          e_rev.flow_ += taken;
          if (e.flow_ == 0) {
            start += 1;
          }
          return taken;
        } else {
          start += 1;
        }
      }

      return 0;
    };

    FlowType taken;
    while ((taken = Dfs(Dfs, start_, std::numeric_limits <FlowType>::max())) > 0) {
      timer += 1;
      std::reverse(begin(path), end(path));
      decomposition.emplace_back(path, taken);
      path.clear();
    }

    return decomposition;
  }

private:
  bool Bfs() {
    std::fill(begin(distance_), end(distance_), -1);

    distance_[start_] = 0;
    auxiliary_queue_.push(start_);
    while (!auxiliary_queue_.empty()) {
      int node = auxiliary_queue_.front();
      auxiliary_queue_.pop();
      for (const int& id : adj_[node]) {
        Edge& e = edges_[id];
        if (distance_[e.to_] == -1
            && lower_bound_ <= e.GetPotential()) {
          distance_[e.to_] = distance_[node] + 1;
          auxiliary_queue_.push(e.to_);
        }
      }
    }

    if (distance_[terminal_] == -1) {
      return false;
    }
    std::fill(begin(first_alive_edge_), end(first_alive_edge_), 0);
    return true;
  }

  FlowType Dfs(int node, FlowType augment) {
    if (node == terminal_) {
      return augment;
    }

    int id;
    FlowType pushed;
    int& start = first_alive_edge_[node];

    for (int i = start; i < ssize(adj_[node]); ++i) {
      id = adj_[node][i];
      Edge& e = edges_[id];
      Edge& e_rev = edges_[id ^ 1];

      if (distance_[node] + 1 != distance_[e.to_]
          || e.GetPotential() < lower_bound_) {
        start += 1;
        continue;
      }

      pushed = Dfs(e.to_, std::min(augment, e.GetPotential()));
      if (pushed > 0) {
        e.flow_ += pushed;
        e_rev.flow_ -= pushed;
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

  FlowType lower_bound_ = 1;

  int n_;
  std::vector <Edge> edges_;
  std::vector <int> distance_;
  std::queue <int> auxiliary_queue_;
  std::vector <int> first_alive_edge_;
  std::vector <std::vector <int>> adj_;
};

void RunCase() {
  int n, m;
  std::cin >> n >> m;

  FlowGraph <int> g(0, n - 1, n, m);
  for (int i = 0; i < m; ++i) {
    int from, to, cap;
    std::cin >> from >> to >> cap;
    --from; --to;
    g.AddBidirectionalEdge(from, to, cap);
  }

  std::cout << g.Dinic() << "\n";
  for (int i = 0; i < m; ++i) {
    std::cout << g.GetEdge(2 * i).value().flow_ << "\n";
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
