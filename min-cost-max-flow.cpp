#include <bits/stdc++.h>

template <typename FlowType, typename CostType>
class MinCostMaxFlowNetwork {
public:
  class Edge {
  public:
    Edge() = default;
    Edge(int from, int to,
         CostType cost, FlowType capacity)
    : from_(from),
      to_(to),
      cost_(cost),
      capacity_(capacity) {
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
    inline FlowType GetFlow() const {
      return flow_;
    }

    [[nodiscard]]
    inline FlowType GetCapacity() const {
      return capacity_;
    }

    [[nodiscard]]
    inline FlowType GetPotential() const {
      return capacity_ - flow_;
    }

    [[nodiscard]]
    inline CostType GetCost() const {
      return cost_;
    }

    inline void AddFlow(const FlowType& increment) {
      flow_ += increment;
    }

    int from_;
    int to_;
    CostType cost_;
    FlowType flow_{};
    FlowType capacity_;
  };

  MinCostMaxFlowNetwork() = delete;
  MinCostMaxFlowNetwork(int start, int terminal,
                        int vertices, int edges = -1)
 : start_(start),
   terminal_(terminal),
   n_(vertices),
   adj_(vertices),
   sp_distance_(vertices),
   sp_previous_edge_(vertices) {
    if (edges != -1) {
      edges_.reserve(edges * 2);
    }
  }

  inline int AddEdge(int from, int to, CostType cost, FlowType cap) {
    edges_alive_ += 1;
    edges_.emplace_back(from, to, cost, cap);
    adj_[from].emplace_back(ssize(edges_) - 1);
    edges_.emplace_back(to, from, -cost, 0);
    adj_[to].emplace_back(ssize(edges_) - 1);
    return adj_[from].back();
  }

  std::pair <FlowType, CostType> MCMF() {
    FlowType total_flow = 0;
    CostType total_cost = 0;

    std::vector <CostType> potentials(n_);

    {
      std::vector <int> order(ssize(edges_) / 2);
      std::iota(begin(order), end(order), 0);
      std::shuffle(begin(order), end(order), std::mt19937(std::chrono::steady_clock::now().time_since_epoch().count()));

      while (true) {
        bool relaxation = false;
        for (const int& id : order) {
          const Edge& e = edges_[id * 2];
          if (potentials[e.to_] > potentials[e.from_] + e.cost_) {
            relaxation = true;
            potentials[e.to_] = potentials[e.from_] + e.cost_;
          }
        }
        if (!relaxation) {
          break;
        }
      }

      ApplyPotentials(potentials);
    }

    while (Dijkstra()) {
      FlowType pushed = std::numeric_limits<FlowType>::max();

      {
        int id;
        int current_node = terminal_;
        while (current_node != start_) {
          id = sp_previous_edge_[current_node];
          const Edge& e = edges_[id];
          pushed = std::min(pushed, e.GetPotential());
          current_node = e.from_;
        }
      }

      {
        int id;
        int current_node = terminal_;
        while (current_node != start_) {
          id = sp_previous_edge_[current_node];
          Edge& e = edges_[id];
          Edge& e_rev = edges_[id ^ 1];

          e.AddFlow(pushed);
          if (e.GetPotential() == 0) {
            edges_alive_ -= 1;
          }
          if (e_rev.GetPotential() == 0) {
            edges_alive_ += 1;
          }
          e_rev.AddFlow(-pushed);

          total_cost += pushed * (e.cost_ - potentials[e.from_] + potentials[e.to_]);
          current_node = e.from_;
        }
      }

      total_flow += pushed;
      for (int i = 0; i < n_; ++i) {
        if (sp_distance_[i] == std::numeric_limits <CostType>::max()) {
          sp_distance_[i] = 0;
        }
        potentials[i] += sp_distance_[i];
      }

      ApplyPotentials(sp_distance_);
    }

    return {total_flow, total_cost};
  }

private:
  void DenseDijkstra() {
    std::vector <char> used_(n_);
    auto Relax = [&](const int& node) -> void {
      used_[node] = true;
      for (const int& id : adj_[node]) {
        const Edge& e = edges_[id];
        if (e.GetPotential() > 0 && sp_distance_[e.to_] > sp_distance_[e.from_] + e.cost_) {
          sp_previous_edge_[e.to_] = id;
          sp_distance_[e.to_] = sp_distance_[e.from_] + e.cost_;
        }
      }
    };

    Relax(0);
    int first_unused = 1;
    while (first_unused < n_) {
      int cheapest_node = first_unused;
      CostType min_cost = sp_distance_[cheapest_node];
      for (int j = cheapest_node + 1; j < n_; ++j) {
        if (used_[j]) {
          continue;
        }
        if (sp_distance_[j] < min_cost) {
          cheapest_node = j;
          min_cost = sp_distance_[j];
        }
      }

      if (sp_distance_[cheapest_node] == std::numeric_limits <CostType>::max()) {
        break;
      }

      Relax(cheapest_node);
      if (cheapest_node == first_unused) {
        while (first_unused < n_ && used_[first_unused]) {
          first_unused += 1;
        }
      }
    }
  }

  void SparseDijkstra() {
    std::priority_queue <std::pair <CostType, int>, std::vector <std::pair <CostType, int>>, std::greater<>> heap;

    heap.emplace(0, start_);
    while (!heap.empty()) {
      auto [dist, node] = heap.top();
      heap.pop();
      if (dist != sp_distance_[node]) {
        continue;
      }

      for (const int& id : adj_[node]) {
        const Edge& e = edges_[id];
        if (e.GetPotential() > 0 &&
            sp_distance_[e.to_] > sp_distance_[node] + e.cost_) {
          sp_previous_edge_[e.to_] = id;
          sp_distance_[e.to_] = sp_distance_[node] + e.cost_;
          heap.emplace(sp_distance_[e.to_], e.to_);
        }
      }
    }

  }

  bool Dijkstra() {
    std::fill(begin(sp_distance_), end(sp_distance_), std::numeric_limits <CostType>::max());
    sp_distance_[start_] = 0;

    long long evaluate_dense = (long long)n_ * n_;
    long long evaluate_sparse = (long long)edges_alive_ * std::__lg(edges_alive_) * 4;

    if (evaluate_dense < evaluate_sparse) {
      DenseDijkstra();
    } else {
      SparseDijkstra();
    }

    return sp_distance_[terminal_] != std::numeric_limits <CostType>::max();
  }

  void ApplyPotentials(const std::vector <CostType>& potentials) {
    for (Edge& e : edges_) {
      e.cost_ += potentials[e.from_] - potentials[e.to_];
    }
  }

  int n_;
  int edges_alive_{};
  std::vector <Edge> edges_;
  std::vector <CostType> sp_distance_;
  std::vector <int> sp_previous_edge_;
  std::vector <std::vector <int>> adj_;

  const int start_;
  const int terminal_;
};

void RunCase() {
  int n, m;
  std::cin >> n >> m;

  MinCostMaxFlowNetwork <int, long long> network(0, n - 1, n, m);
  for (int i = 0; i < m; ++i) {
    int from, to, cap, cost;
    std::cin >> from >> to >> cap >> cost;
    --from; --to;
    network.AddEdge(from, to, cost, cap);
  }

  std::cout << network.MCMF().second << "\n";
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
