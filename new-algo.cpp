#include "stdc++.h"

using namespace std;

const int MAX_VERTICES = 1e5 + 10;
const int MAX_EDGES = 1e6 + 10;
const int MAX_PARTITIONS = 20;
const int INF = (int) 2e9 + 7;
const float ALPHA = 0.5;

// Raw big graph data
int num_edges, num_vertices, num_partitions;
vector<int> adj[MAX_VERTICES];
pair<int, int> edges[MAX_EDGES];

// Partition data
int in_partition[MAX_VERTICES];
set<int> in_vertices[MAX_PARTITIONS];
set<int> out_vertices[MAX_PARTITIONS];

int cost_in_partition[MAX_PARTITIONS];

// Special cost is cost was defined by researcher
int special_partition_costs[MAX_PARTITIONS];

// Cross-graph data
int num_cg_edges, num_cg_vertices;
vector<int> cg_adj[MAX_VERTICES];
pair<int, int> cg_edges[MAX_EDGES];
int cg_total_cost[MAX_VERTICES];
vector<int> cg_vertices;

// Depend-graph data
int num_dg_edges, num_dg_vertices;
int average_cost_depend_graph;
vector<int> dg_vertices;
vector<int> dg_adj[MAX_VERTICES];
int dg_each_vertex_cost[MAX_VERTICES];
map<pair<int, int>, bool> in_vertice_to_out_vertice;

// Best result through all optimizing loop
int max_difference_cost;
int max_cost;
int answer_partitions[MAX_VERTICES];
int answer_special_costs[MAX_PARTITIONS];
vector<int> answer_dg_vertices;
int answer_depend_graph_costs[MAX_VERTICES];
int answer_average_depend_graph_cost;

void input_data()
{
  cin >> num_vertices >> num_edges >> num_partitions;
  for (int i = 1; i <= num_edges; ++i) {
    int from, to;
    cin >> from >> to;
    adj[from].push_back(to);
    edges[i] = {from, to};
  }

  for (int i = 1; i <= num_vertices; ++i) {
    sort(adj[i].begin(), adj[i].end());
  }
}

int calc_raised_weight_internal(int v, int p) 
{
  int total = 0;
  for (auto u : adj[v]) {
    if (in_partition[u] == p) {
      total += 1;
    }
  }
  return cost_in_partition[p] + total;
}

int calc_raised_cut_edge(int v, int p) 
{
  int total = 0;
  for (auto u : adj[v]) {
    if (in_partition[u] != p && in_partition[u] != -1) {
      total += 1;
    }
  }
  return total - calc_raised_weight_internal(v, p);
}

int greedy_function(const vector<int> &V, const int &p) {
  int mn = INF;
  vector<int> C;
  for (int v : V) {
    int m = calc_raised_cut_edge(v, p);
    if (m < mn) {
      mn = m;
      C.clear();
      C.push_back(v);
    } else if (m == mn) {
      C.push_back(v);
    }
  }
  random_device rd;
  mt19937 g(rd());
  std::shuffle(C.begin(), C.end(), g);
  return C.back();
}

void partitioning()
{
  memset(in_partition, -1, sizeof in_partition);
  vector<vector<int>> P(num_partitions);
  vector<int> V;

  for (int i = 1; i <= num_vertices; ++i) {
    V.push_back(i);
  }

  for (int i = 0; i < num_partitions; ++i) {
    int r_pos = rand() % ((int) V.size());
    P[i].push_back(*(V.begin() + r_pos));
    in_partition[*(V.begin() + r_pos)] = i;
    V.erase(V.begin() + r_pos);
  }

  int p = 0;
  while ((int) V.size() > 0) {
    int b = greedy_function(V, p);
    P[p].push_back(b);
    in_partition[b] = p;
    cost_in_partition[p] = calc_raised_weight_internal(b, p);
    auto it = find(V.begin(), V.end(), b);
    V.erase(it);
    p = (p + 1) % num_partitions;
  }

  for (int i = 1; i <= num_vertices; ++i) {
    in_partition[i]++;
  }
}

int bfs_special_partition_costs(int vertex, int partition_id) 
{
  // queue keeps only vertices
  queue<int> bfs_queue;
  bfs_queue.push(vertex);

  unordered_map<int, bool> was;
  was[vertex] = true;
  
  int num_of_out_vertice = 0;
  int cost_of_traversal_process = 0;

  while (!bfs_queue.empty()) {
    int current_vertex = bfs_queue.front();
    bfs_queue.pop();
    
    for (auto next_vertex : adj[current_vertex]) {
      cost_of_traversal_process++;
      if (was[next_vertex]) continue;
      was[next_vertex] = true;
      if (in_partition[next_vertex] == partition_id) {
        bfs_queue.push(next_vertex);
      } 
      else {
        in_vertice_to_out_vertice[{vertex, next_vertex}] = true;
        num_of_out_vertice++;
      }
    }

    if (num_of_out_vertice >= out_vertices[partition_id].size()) {
      break;
    }
  }

  return cost_of_traversal_process;
}
  
void build_in_out_sets() 
{
  for (int i = 1; i <= num_edges; ++i) {
    int u = edges[i].first;
    int v = edges[i].second;
    if (in_partition[u] != in_partition[v]) {
      in_vertices[in_partition[v]].insert(v);
      out_vertices[in_partition[u]].insert(v);  
    }
  }
}

void calculate_costs_in_partition() 
{
  for (int i = 1; i <= num_partitions; ++i) {
    in_vertices[i].clear();
    out_vertices[i].clear();
  }

  build_in_out_sets();

  for (int i = 1; i <= num_partitions; ++i) {
    special_partition_costs[i] = 0;
    for (auto node : in_vertices[i]) {
      special_partition_costs[i] += bfs_special_partition_costs(node, i);
    }
  }
}

void build_cross_graph()
{
  map<pair<int, int>, bool> has_edge;
  map<int, bool> has_vertex;
  num_cg_vertices = 0;
  
  for (int i = 1; i <= num_edges; ++i) {
    int from = edges[i].first;
    int to = edges[i].second;
    if (answer_partitions[from] != answer_partitions[to] && !has_edge[{from, to}]) {
      if (!has_vertex[from]) {
        cg_vertices.push_back(from);
        has_vertex[from] = true;
      }

      if (!has_vertex[to]) {
        cg_vertices.push_back(to);
        has_vertex[to] = true;
      }

      cg_adj[from].push_back(to);
      cg_edges[++num_cg_edges] = {from, to};
      has_edge[{from, to}] = true;
    }
  }
}

int bfs_cross_graph(int cg_vertex) 
{
  queue<pair<int, int>> bfs_queue;
  map<int, bool> was;
  bfs_queue.push({cg_vertex, 0});
  was[cg_vertex] = true;

  int total_cost = 0;

  while (!bfs_queue.empty()) {
    int current_cg_vertex = bfs_queue.front().first;
    int current_cost = bfs_queue.front().second;
    bfs_queue.pop();
    total_cost += current_cost;
    for (int next_vertex : cg_adj[current_cg_vertex]) {
      if (was[next_vertex]) continue;
      was[next_vertex] = true;
      bfs_queue.push({next_vertex, current_cost + 1});
    }
  }

  return total_cost;
}

void calculate_costs_in_cross_graph()
{
  for (size_t i = 0; i < cg_vertices.size(); ++i) {
    cg_total_cost[i] += bfs_cross_graph(cg_vertices[i]);
  }
}

void dfs_find_best_node(
  int u, 
  int partition_id, 
  map<int, bool> &visited_node, 
  map<pair<int, int>, bool> &visited_edge, 
  vector<int> &temp,
  long long &sum)
{
  temp.push_back(u);
  for (auto v : adj[u]) {
    if (visited_edge[{u, v}]) continue;
    sum++;
    visited_edge[{u, v}] = true;

    if (in_partition[v] == partition_id && !visited_node[v]) {
      visited_node[v] = true;
      dfs_find_best_node(v, partition_id, visited_node, visited_edge, temp, sum);
    }
  }
}

double calc_heuristic(int node, const int &sum, const vector<int> &temp){      
  int direc = 0; 
  for (int v : temp) {
    if (binary_search(adj[node].begin(), adj[node].end(), v)) {
      direc++;
    }
  }
  return (double) 1.0 * sum / (direc + 1);       
}

int find_best_in_node(int partition_id) 
{
  map<int, bool> visited_node;
  map<pair<int, int>, bool> visited_edge;
  vector<pair<double, int>> heuristic;

  int best_vertex = 0;
  for (auto u : in_vertices[partition_id]) {
    if (visited_node[u]) continue;
    visited_node[u] = true;
    vector<int> temp;
    long long sum = 0;
    dfs_find_best_node(u, partition_id, visited_node, visited_edge, temp, sum);
    for (int i = 0; i < (int) temp.size(); ++i) {
      heuristic.push_back({calc_heuristic(temp[i], sum, temp), temp[i]});
    }
  }

  double highest_heuristic = -1.0;
  for (int i = 0; i < (int) heuristic.size(); ++i) {
    if (heuristic[i].first > highest_heuristic) {
      best_vertex = heuristic[i].second;
      highest_heuristic = heuristic[i].first;
    }
  }
  return best_vertex;
}

void optimize_func() 
{ // This function is choosing best "in_vertices" of partition and move it to other partition
  pair<int, int> max_partition_cost = {special_partition_costs[1], 1};
  pair<int, int> min_partition_cost = {special_partition_costs[1], 1};
  for (int i = 2; i <= num_partitions; ++i) {
    if (max_partition_cost.first < special_partition_costs[i]) {
      max_partition_cost = {special_partition_costs[i], i};
    }

    if (min_partition_cost.first > special_partition_costs[i]) {
      min_partition_cost = {special_partition_costs[i], i};
    }
  }

  int node_to_move = find_best_in_node(max_partition_cost.second);

  in_partition[node_to_move] = min_partition_cost.second;
}

void get_best_answer() 
{
  int max_cost = *max_element(special_partition_costs + 1, special_partition_costs + 1 + num_partitions);
  int min_cost = *min_element(special_partition_costs + 1, special_partition_costs + 1 + num_partitions);
  int delta = max_cost - min_cost;
  if (delta < max_difference_cost) {
    max_difference_cost = delta;
    for (int i = 1; i <= num_vertices; ++i) {
      answer_partitions[i] = in_partition[i];
    }
      
    for (int i = 1; i <= num_partitions; ++i) {
      answer_special_costs[i] = special_partition_costs[i];
    }
  }  
}

void get_best_answer_by_minimize_max_cost() 
{
  int current_max_cost = *max_element(special_partition_costs + 1, special_partition_costs + 1 + num_partitions);
  if (current_max_cost < max_cost) {
    max_cost = current_max_cost;
    for (int i = 1; i <= num_vertices; ++i) {
      answer_partitions[i] = in_partition[i];
    }
      
    for (int i = 1; i <= num_partitions; ++i) {
      answer_special_costs[i] = special_partition_costs[i];
    }
  }
}

void get_best_answer_by_alpha(int alpha) {
  int max_special_cost = *max_element(special_partition_costs + 1, special_partition_costs + 1 + num_partitions);
  
  int current_max_cost = alpha * max_special_cost + (1 - alpha) * average_cost_depend_graph;
  
  if (current_max_cost < max_cost) {
    max_cost = current_max_cost;
    for (int i = 1; i <= num_vertices; ++i) {
      answer_partitions[i] = in_partition[i];
    }
      
    for (int i = 1; i <= num_partitions; ++i) {
      answer_special_costs[i] = special_partition_costs[i];
    }

    answer_dg_vertices.clear();
    for (int node : dg_vertices) {
      answer_dg_vertices.push_back(node);
      answer_depend_graph_costs[node] = dg_each_vertex_cost[node];
      answer_average_depend_graph_cost = average_cost_depend_graph;
    }
  }
}

int bfs_depend_graph(int dg_vertex){
  queue<int> bfs_queue;
  map<int, bool> was;
  bfs_queue.push(dg_vertex);
  was[dg_vertex] = true;

  int total_cost = 0;

  while (!bfs_queue.empty()) {
    int current_dg_vertex = bfs_queue.front();
    bfs_queue.pop();
    for (int next_vertex : dg_adj[current_dg_vertex]) {
      total_cost ++;
      if (was[next_vertex]) continue;
      was[next_vertex] = true;
      bfs_queue.push(next_vertex);
    }
  }

  return total_cost;
}

void build_edge_of_depend_graph() {
  for (int id_partition = 1; id_partition<=num_partitions; id_partition++) {
    for (int in_node : in_vertices[id_partition]) {
      dg_adj[in_node].clear();
      for (int out_node : out_vertices[id_partition]) {
        if (in_vertice_to_out_vertice[{in_node, out_node}]) {
          dg_adj[in_node].push_back(out_node);
        }
      }
    }
  }
}

void build_depend_graph() {
  dg_vertices.clear();
  map<int, bool> was;

  for (int id_partition = 1; id_partition<=num_partitions; ++id_partition) {
    for (int node : in_vertices[id_partition]) {
      if (!was[node]) {
        was[node] = true;
        dg_vertices.push_back(node);
      }
    }

    for (int node : out_vertices[id_partition]) {
      if (!was[node]) {
        was[node] = true;
        dg_vertices.push_back(node);
      }
    }
  }

  build_edge_of_depend_graph();
}

void calculate_average_costs_in_depend_graph() {
  build_depend_graph();

  long long total_cost = 0;

  for (int node : dg_vertices) {
    long long temp = bfs_depend_graph(node);
    dg_each_vertex_cost[node] = temp;
    total_cost += temp;
  }

  average_cost_depend_graph = total_cost / dg_vertices.size();
}

void run_optimizing() 
{
  int max_loop = 1000;
  max_difference_cost = INF;
  max_cost = INF;

  for (int loop = 1; loop <= max(max_loop, num_vertices*4); ++loop) {
    if (loop % 100 == 0) {
      cerr << "Running at " << loop << "th loop" << endl;
    }

    in_vertice_to_out_vertice.clear();
    
    optimize_func();
    calculate_costs_in_partition();
    calculate_average_costs_in_depend_graph();
    get_best_answer_by_alpha(ALPHA);
  }
}

void output_result()
{
  vector<int> num_vertices_in_partition(num_partitions + 1);
  for (int i = 1; i <= num_vertices; ++i) {
    num_vertices_in_partition[answer_partitions[i]]++;
  }

  cout << "Answer postition: " << endl;
  for (int i = 1; i <= num_vertices; ++i) {
    cout << answer_partitions[i] << " ";
  }
  cout << endl;

  cout << "Number of vertices in each partition:" << endl;
  for (int i = 1; i <= num_partitions; ++i) {
    cout << "V[" << i << "] = " << num_vertices_in_partition[i] << endl;
  }

  cout << "Special partition costs: " << endl;
  for (int i = 1; i <= num_partitions; ++i) {
    cout << answer_special_costs[i] << " ";
  }
  cout << endl;

  cout << "Number vertices in cross graph: " << cg_vertices.size() << endl;

  // cout << "Cost in cross graph: " << endl;
  // for (size_t i = 0; i < cg_vertices.size(); ++i) {
  //   cout << cg_vertices[i] << ": " << cg_total_cost[i] << "\n";
  // }
  
  cout << "Number vertices in depend graph is: " << answer_dg_vertices.size() << endl;

  cout << "Cost of depend graph: " << endl;
  for (int node : answer_dg_vertices) {
    cout << node << ": " << answer_depend_graph_costs[node] << endl;
  }
  
  cout << "Average cost in depend graph is: " << answer_average_depend_graph_cost << endl;
}


// [[deprecated("This function only use for testing")]]
void fake_result()
{
  answer_partitions[1] = 3;
  answer_partitions[2] = 3;
  answer_partitions[3] = 3;
  answer_partitions[4] = 3;
  answer_partitions[5] = 3;
  answer_partitions[6] = 3;
  answer_partitions[7] = 1;
  answer_partitions[8] = 1;
  answer_partitions[9] = 1;
  answer_partitions[10] = 1;
  answer_partitions[11] = 3;
  answer_partitions[12] = 2;
  answer_partitions[13] = 2;
  answer_partitions[14] = 2;
  answer_partitions[15] = 2;
  answer_partitions[16] = 2;
}

[[deprecated("This function only use for testing")]]
void output_fake_result()
{
  // for (int i = 1; i <= num_partitions; ++i) {
  //   cout << special_partition_costs[i] << " ";
  // }
  int num_dg_vertices = 0;
  int total_cost = 0;
  for (int i = 0; i<dg_vertices.size(); ++i) {
    if (dg_each_vertex_cost[dg_vertices[i]]){
      num_dg_vertices ++;
      total_cost += dg_each_vertex_cost[dg_vertices[i]];
    }
  }
  cout << "Number vertices in depend graph: " << dg_vertices.size() << endl;
  for (auto vertext: dg_vertices) {
    cout << vertext << ": " << dg_each_vertex_cost[vertext] << endl;
  }
  cout << "Cost of depend graph (sum) is: " << 1.0*total_cost << endl;

  cout << "Cost of depend graph (average) is: " << 1.0*total_cost/dg_vertices.size() <<endl;
}

int main()
{
  auto start = std::chrono::high_resolution_clock::now();
  
  srand(time(NULL));
  ios::sync_with_stdio(false);  cin.tie(0);

  input_data();

  fake_result();
  // partitioning();

  // calculate_costs_in_partition();

  // calculate_average_costs_in_depend_graph();
  
  // run_optimizing();

  build_cross_graph();

  // calculate_costs_in_cross_graph();

  output_result();
  // output_fake_result();

  auto finish = std::chrono::high_resolution_clock::now();
  std::chrono::duration<double> elapsed = finish - start;
  cout << "Algorithm run in " << elapsed.count() << "s" << endl;
  return 0;
}
