#include <bits/stdc++.h>

template <typename T, typename U>
class MinCostMaxFlowNetwork {
public:
  using FlowType = T;
  using CostType = U;

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
          e.AddFlow(pushed);
          BackEdge(id).AddFlow(-pushed);
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
  bool Dijkstra() {
    std::fill(begin(sp_distance_), end(sp_distance_), std::numeric_limits <T>::max());
    sp_distance_[start_] = 0;

    heap_.emplace(0, start_);
    while (!heap_.empty()) {
      auto [dist, node] = heap_.top();
      heap_.pop();
      if (dist != sp_distance_[node]) {
        continue;
      }

      for (const int& id : adj_[node]) {
        const Edge& e = edges_[id];
        if (e.GetPotential() > 0 &&
            sp_distance_[e.to_] > sp_distance_[node] + e.cost_) {
          sp_previous_edge_[e.to_] = id;
          sp_distance_[e.to_] = sp_distance_[node] + e.cost_;
          heap_.emplace(sp_distance_[e.to_], e.to_);
        }
      }
    }

    return sp_distance_[terminal_] != std::numeric_limits <T>::max();
  }

  Edge& BackEdge(int id) {
    return edges_[id ^ 1];
  }

  void ApplyPotentials(const std::vector <CostType>& potentials) {
    for (Edge& e : edges_) {
      e.cost_ += potentials[e.from_] - potentials[e.to_];
    }
  }

  int n_;
  std::vector <Edge> edges_;
  std::vector <CostType> sp_distance_;
  std::vector <CostType> sp_previous_edge_;
  std::vector <std::vector <int>> adj_;
  std::priority_queue <std::pair <CostType, int>, std::vector <std::pair <CostType, int>>, std::greater<>> heap_;

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
