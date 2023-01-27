\#include <bits/stdc++.h>

/* Computes MCMF in O(|max_flow| * Dijkstra)
 * Doesn't work for graphs with negative cycles */
template <typename FlowType, typename CostType>
class MinCostMaxFlowNetwork {
public:
  class Edge {
  public:
    Edge() = default;
    Edge(int from, int to,
         FlowType capacity, CostType cost)
        : from_(from),
          to_(to),
          cost_(cost),
          capacity_(capacity) {
    }

    [[nodiscard]]
    inline FlowType GetRemainingFlow() const {
      return capacity_ - flow_;
    }

    [[nodiscard]]
    inline CostType GetCost() const {
      return cost_ - potential_;
    }

    void ApplyPotential(const CostType& from_potential,
                        const CostType& to_potential) {
      CostType delta = from_potential - to_potential;
      cost_ += delta;
      potential_ += delta;
    }

    int from_{};
    int to_{};
    FlowType flow_{};
    FlowType capacity_;
    CostType cost_;
    CostType potential_{};
  };

  MinCostMaxFlowNetwork(int start, int terminal,
                        int vertices, int edges = -1)
      : start_(start),
        terminal_(terminal),
        n_(vertices),
        adj_(vertices),
        used_(vertices),
        sp_distance_(vertices),
        sp_weighted_distance_(vertices),
        sp_previous_edge_(vertices) {
    if (edges != -1) {
      edges_.reserve(edges * 2);
    }
  }

  int AddEdge(int from, int to, FlowType cap, CostType cost) {
    edges_alive_ += 1;
    edges_.emplace_back(from, to, cap, cost);
    adj_[from].emplace_back(ssize(edges_) - 1);
    edges_.emplace_back(to, from, 0, -cost);
    adj_[to].emplace_back(ssize(edges_) - 1);
    return adj_[from].back();
  }

  [[nodiscard]]
  const Edge& GetEdge(int id) const {
    return edges_[id];
  }

  std::optional <CostType> MinCostKFlow(FlowType k) {
    FlowType k_flow = 0;
    FlowType min_cost = 0;

    bool negative_edge = false;
    for (int i = 0; i < ssize(edges_); i += 2) {
      if (edges_[i].cost_ < 0) {
        negative_edge = true;
        break;
      }
    }

    if (negative_edge) {
      std::vector <int> order(size(edges_));
      std::iota(begin(order), end(order), 0);
      std::shuffle(begin(order), end(order), std::forward <std::mt19937>(std::mt19937(std::chrono::steady_clock::now().time_since_epoch().count())));

      bool relaxation = true;
      while (relaxation) {
        relaxation = false;
        for (const int& id : order) {
          const Edge& e = edges_[id];
          if (sp_weighted_distance_[e.to_] > sp_weighted_distance_[e.from_] + e.cost_) {
            relaxation = true;
            sp_weighted_distance_[e.to_] = sp_weighted_distance_[e.from_] + e.cost_;
          }
        }
      }

      ApplyPotentials();
    }

    std::vector <int> path;
    while (Dijkstra() && k_flow < k) {
      path.reserve(sp_distance_[terminal_]);
      FlowType pushed = std::numeric_limits <FlowType>::max();

      {
        int id;
        int current_node = terminal_;
        while (current_node != start_) {
          id = sp_previous_edge_[current_node];
          path.push_back(id);
          current_node = edges_[id].from_;
          pushed = std::min(pushed, edges_[id].GetRemainingFlow());
        }
      }

      pushed = min(pushed, k - k_flow);
      for (const int& id : path) {
        Edge& e = edges_[id];
        Edge& e_rev = edges_[id ^ 1];

        e.flow_ += pushed;
        e_rev.flow_ -= pushed;
        if (e.flow_ == e.capacity_) {
          edges_alive_ -= 1;
        }
        if (e_rev.flow_ == e_rev.capacity_ - pushed) {
          edges_alive_ += 1;
        }
        min_cost += pushed * e.GetCost();
      }

      path.clear();
      k_flow += pushed;
      std::for_each(begin(sp_weighted_distance_), end(sp_weighted_distance_),
                    [&](CostType& c) {
                      if (c == std::numeric_limits <CostType>::max()) {
                        c = 0;
                      }
                    });
      ApplyPotentials();
    }

    if (k_flow < k) {
      return std::nullopt;
    } else {
      return min_cost;
    };
  }

  /* Decomposes the found flow to paths. Runs in O(VE) */
  std::vector <std::pair <std::vector <int>, FlowType>> FlowDecomposition() {
    std::vector <int> path; /* indices of edges*/
    std::vector <std::pair <std::vector <int>, FlowType>> decomposition;

    int timer = 0;
    std::vector <int> used(n_, -1);
    std::vector <int> first_alive_edge(n_, 0);

    auto Dfs = [&](const auto& Self, int node, FlowType path_min) -> FlowType {
      if (node == terminal_) {
        return path_min;
      }

      if (used[node] == timer) {
        return path_min;
      }

      int id;
      FlowType taken;
      used[node] = timer;
      int& start = first_alive_edge[node];

      for (int i = start; i < ssize(adj_[node]); ++i) {
        id = adj_[node][i];
        Edge& e = edges_[id];
        Edge& e_rev = edges_[id ^ 1];
        if (e.flow_ > 0 && (taken = Self(Self, e.to_, std::min(path_min, e.flow_))) > 0) {
          path.emplace_back(id);
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

  std::pair <FlowType, CostType> MinCostMaxFlow() {
    FlowType max_flow = 0;
    FlowType min_cost = 0;

    bool negative_edge = false;
    for (int i = 0; i < ssize(edges_); i += 2) {
      if (edges_[i].cost_ < 0) {
        negative_edge = true;
        break;
      }
    }

    if (negative_edge) {
      std::vector <int> order(size(edges_));
      std::iota(begin(order), end(order), 0);
      std::shuffle(begin(order), end(order), std::forward <std::mt19937>(std::mt19937(std::chrono::steady_clock::now().time_since_epoch().count())));

      bool relaxation = true;
      while (relaxation) {
        relaxation = false;
        for (const int& id : order) {
          const Edge& e = edges_[id];
          if (sp_weighted_distance_[e.to_] > sp_weighted_distance_[e.from_] + e.cost_) {
            relaxation = true;
            sp_weighted_distance_[e.to_] = sp_weighted_distance_[e.from_] + e.cost_;
          }
        }
      }

      ApplyPotentials();
    }

    std::vector <int> path;
    while (Dijkstra()) {
      path.reserve(sp_distance_[terminal_]);
      FlowType pushed = std::numeric_limits <FlowType>::max();

      {
        int id;
        int current_node = terminal_;
        while (current_node != start_) {
          id = sp_previous_edge_[current_node];
          path.push_back(id);
          current_node = edges_[id].from_;
          pushed = std::min(pushed, edges_[id].GetRemainingFlow());
        }
      }

      max_flow += pushed;
      for (const int& id : path) {
        Edge& e = edges_[id];
        Edge& e_rev = edges_[id ^ 1];

        e.flow_ += pushed;
        e_rev.flow_ -= pushed;
        if (e.flow_ == e.capacity_) {
          edges_alive_ -= 1;
        }
        if (e_rev.flow_ == e_rev.capacity_ - pushed) {
          edges_alive_ += 1;
        }
        min_cost += pushed * e.GetCost();
      }

      path.clear();
      std::for_each(begin(sp_weighted_distance_), end(sp_weighted_distance_),
                    [&](CostType& c) {
                      if (c == std::numeric_limits <CostType>::max()) {
                        c = 0;
                      }
                    });
      ApplyPotentials();
    }

    return {max_flow, min_cost};
  }
  
private:
  void DenseDijkstra() {
    for (int i = 0; i < n_; ++i) {
      int cheapest_node = 0;
      while (used_[cheapest_node]) {
        cheapest_node += 1;
      }

      CostType min_cost = sp_weighted_distance_[cheapest_node];
      for (int j = cheapest_node + 1; j < n_; ++j) {
        if (used_[j]) {
          continue;
        }
        if (sp_weighted_distance_[j] < min_cost) {
          cheapest_node = j;
          min_cost = sp_weighted_distance_[j];
        }
      }

      used_[cheapest_node] = true;
      if (sp_weighted_distance_[cheapest_node] == std::numeric_limits <CostType>::max()) {
        break;
      }

      for (const int& id : adj_[cheapest_node]) {
        const Edge& e = edges_[id];
        if (e.GetRemainingFlow() > 0
            && sp_weighted_distance_[e.to_] > sp_weighted_distance_[e.from_] + e.cost_) {
          sp_previous_edge_[e.to_] = id;
          sp_distance_[e.to_] = sp_distance_[e.from_] + 1;
          sp_weighted_distance_[e.to_] = sp_weighted_distance_[e.from_] + e.cost_;
        }
      }
    }

    std::fill(begin(used_), end(used_), 0);
  }

  void SparseDijkstra() {
    heap_.emplace(0, start_);
    while (!heap_.empty()) {
      const auto [distance, node] = heap_.top();
      heap_.pop();

      if (sp_weighted_distance_[node] != distance) {
        continue;
      }

      for (const int& id : adj_[node]) {
        const Edge& e = edges_[id];
        if (e.GetRemainingFlow() > 0
            && sp_weighted_distance_[e.to_] > sp_weighted_distance_[e.from_] + e.cost_) {
          sp_previous_edge_[e.to_] = id;
          sp_distance_[e.to_] = sp_distance_[e.from_] + 1;
          sp_weighted_distance_[e.to_] = sp_weighted_distance_[e.from_] + e.cost_;
          heap_.emplace(sp_weighted_distance_[e.to_], e.to_);
        }
      }
    }
  }

  bool Dijkstra() {
    if (edges_alive_ == 0) {
      return false;
    }

    std::fill(begin(sp_weighted_distance_), end(sp_weighted_distance_), std::numeric_limits <CostType>::max());
    sp_weighted_distance_[start_] = sp_distance_[start_] = 0;

    long long dense_evaluation = static_cast <long long>(n_) * n_;
    long long sparse_evaluation = static_cast <long long>(edges_alive_) * std::__lg(edges_alive_);
    if (dense_evaluation < sparse_evaluation) {
      DenseDijkstra();
    } else {
      SparseDijkstra();
    }
    SparseDijkstra();

    return sp_weighted_distance_[terminal_] != std::numeric_limits <CostType>::max();
  }

  void ApplyPotentials() {
    for (Edge& e : edges_) {
      e.ApplyPotential(sp_weighted_distance_[e.from_], sp_weighted_distance_[e.to_]);
    }
  }

  int n_;
  const int start_;
  const int terminal_;

  std::vector <Edge> edges_;
  std::vector <std::vector <int>> adj_;

  /* Dijkstra stuff*/
  int edges_alive_{};
  std::vector <char> used_;
  std::vector <int> sp_distance_;
  std::vector <int> sp_previous_edge_;
  std::vector <CostType> sp_weighted_distance_;
  std::priority_queue <std::pair <CostType, int>, std::vector <std::pair <CostType, int>>, std::greater<>> heap_;
};


void RunCase() {
  
}

int main() {
  std::ios_base::sync_with_stdio(false);
  std::cin.tie(nullptr);
  int tt = 1;
  std::cin >> tt;
  while (tt--) {
    RunCase();
  }
  return 0;
}
