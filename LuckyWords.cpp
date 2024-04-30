#include <iostream>
#include <string>
#include <deque>
#include <vector>
#include <algorithm>
#include <iomanip>
#include <map>
#include <set>
#include <queue>
#include <fstream>
#include <stack>
#include <cmath>
#include <bitset>
#include <unordered_set>
#include <unordered_map>
#include <random>
#include <array>
#include <chrono>
#include <functional>
#include <numeric>
#include <complex>

using namespace std;

#define ll long long
#define ld long double
#define ull uint64_t
#define pll pair<ll, ll>
#define pii pair<int, int>
#define pli pair<ll, int>
#define plli pair<pll, int>
#define pld pair<ld, ld>
#define fst first
#define snd second
#define pdi pair<ld, int>
#define pdd pair<double, double>
#define piii pair<int, pii>

#define forn(i, n) for (int i = 1; i <= n; i++)
#define dforn(i, a, b) for (int i = a; i <= b; i++) 
#define rforn(i, n) for (int i = n; i >= 1; i--)
#define rdforn(i, a, b) for (int i = b; i >= a; i--)
#define sforn(i, a, b, s) for (ll i = a; i <= b; i += s)
#define aforn(v, a) for (auto& v : a)
#define sz(a) ((int)a.size())

const int mod = 998244353;
const ld pi = acos(-1);
const ll N = 2e5;
const ll inf = 3e18;
const int iinf = 1 << 28;
const ld dinf = 1e16;
const double eps = 1e-9;

const int n = 15, m = 200, len = 5, steps = 1000;
random_device rd;
mt19937 gen(rd());
ld rand_rng(ld l, ld r) { return (ld)gen() / gen.max() * (r - l) + l; }
array<array<array<int, m>, n>, steps + 1> dp;
array<array<array<pii, m>, n>, steps + 1> from;
array<array<array<bool, m>, n>, steps + 1> used;

struct Map {
	array<array<char, n>, n> grid;
	array<array<array<piii, 26>, n>, n> greedy_shortest;
	array<vector<pii>, 26> pos;
	Map(array<array<char, n>, n> grd) {
		grid = grd;
		dforn(i, 0, n - 1) dforn(j, 0, n - 1) {
			dforn(c, 0, 25) greedy_shortest[i][j][c] = { iinf, {0, 0} };
			pos[grid[i][j] - 'A'].push_back({ i, j });
		}
		dforn(x, 0, n - 1) dforn(y, 0, n - 1) dforn(nx, 0, n - 1) dforn(ny, 0, n - 1)
			greedy_shortest[x][y][grid[nx][ny] - 'A'] = min(greedy_shortest[x][y][grid[nx][ny] - 'A'], { abs(x - nx) + abs(y - ny) + 1, {nx, ny} });
	}
	int greedy_calc(vector<char> path, int sx, int sy) {
		int dist = 0;
		aforn(v, path) {
			piii nxt = greedy_shortest[sx][sy][v - 'A'];
			dist += nxt.fst;
			sx = nxt.snd.fst, sy = nxt.snd.snd;
		}
		return dist;
	}
	vector<pii> greedy_calc_path(vector<char> path, int sx, int sy) {
		vector<pii> res;
		aforn(v, path) {
			piii nxt = greedy_shortest[sx][sy][v - 'A'];
			res.push_back(nxt.snd);
			sx = nxt.snd.fst, sy = nxt.snd.snd;
		}
		return res;
	}
	//heavy gun
	pair<int, vector<pii>> djkstr_calc(vector<char> path, int sx, int sy, bool f) {
		dforn(it, 0, steps) dforn(i, 0, n - 1) dforn(j, 0, m - 1) dp[it][i][j] = iinf, used[it][i][j] = false;
		priority_queue<pair<int, piii>, vector < pair<int, piii>>, greater<pair<int, piii>>> pq;
		pq.push({ dp[0][sx][sy] = 0, {0, {sx, sy}} });
		int fx = -1, fy = -1;
		while (true) {
			piii h = pq.top().snd;
			pq.pop();
			if (h.fst == sz(path)) {
				fx = h.snd.fst, fy = h.snd.snd;
				break;
			}
			aforn(to, pos[path[h.fst] - 'A']) {
				int ndp = dp[h.fst][h.snd.fst][h.snd.snd] + abs(h.snd.fst - to.fst) + abs(h.snd.snd - to.snd) + 1;
				if (ndp < dp[h.fst + 1][to.fst][to.snd]) pq.push({ dp[h.fst + 1][to.fst][to.snd] = ndp, {h.fst + 1, to} }), from[h.fst + 1][to.fst][to.snd] = h.snd;
			}
		}
		vector<pii> res_path; int res = dp[sz(path)][fx][fy];
		if (f) {
			forn(i, sz(path)) {
				res_path.push_back({ fx, fy });
				int nx = from[sz(path) - i + 1][fx][fy].fst, ny = from[sz(path) - i + 1][fx][fy].snd;
				fx = nx, fy = ny;
			}
			reverse(res_path.begin(), res_path.end());
		}
		return { res, res_path };
	}
};

struct WordsManager {
	array<array<char, len>, m> words;
	array<array<int, m>, m> intersect;
	WordsManager(array<array<char, len>, m> wrds) {
		words = wrds;
		dforn(i, 0, m - 1) dforn(j, 0, m - 1) {
			//if (i == j) continue;
			rdforn(len, 0, 5) {
				bool f = true;
				dforn(k, 0, len - 1) if (words[j][k] != words[i][5 - len + k]) {
					f = false;
					break;
				}
				if (f) {
					intersect[i][j] = len;
					break;
				}
			}
		}
	}
	vector<char> perm_to_path(array<int, m>& perm) {
		vector<char> res;
		dforn(i, 0, m - 1) {
			if (i == 0) dforn(j, 0, 4) res.push_back(words[perm[i]][j]);
			else dforn(j, intersect[perm[i - 1]][perm[i]], 4)  res.push_back(words[perm[i]][j]);
		}
		return res;
	}
};

Map input_map() {
	array<array<char, n>, n> grid;
	dforn(i, 0, n - 1) dforn(j, 0, n - 1) cin >> grid[i][j];
	return Map(grid);
}

WordsManager input_words() {
	array<array<char, len>, m> words;
	dforn(i, 0, m - 1) dforn(j, 0, len - 1) cin >> words[i][j];
	return WordsManager(words);
}

vector<function<vector<pii>(array<int, m>&, int)>> moves;

void rollback(vector<pii>& story, array<int, m>& perm) {
	aforn(v, story) perm[v.fst] = v.snd;
}

array<int, m> PermutationAnnealing(WordsManager& manager, int iter_count, ld tmp, ld cooling) {
	array<int, m> perm, best_perm;
	dforn(i, 0, m - 1) perm[i] = best_perm[i] = i;
	auto calc = [&]() {
		int res = 0;
		dforn(i, 0, m - 2) res += manager.intersect[perm[i]][perm[i + 1]];
		return res;
	};
	int best = calc(), current = best;
	forn(it, iter_count) {
		tmp *= cooling;
		vector<pii> story = moves[0](perm, 5);
		int cand = calc();
		if (cand > current) current = cand;
		else if (rand_rng(0, 1) < exp((cand - current) / tmp)) current = cand;
		else rollback(story, perm);
		if (current > best) best = current, best_perm = perm;
	}
	return best_perm;
}

array<int, m> GreedyAnnealing(Map& letter_map, WordsManager& manager, int sx, int sy, int attempts, int iter_count, ld init_tmp, ld cooling,
	function<vector<pii>(array<int, m>&, int)> move, array<int, m> init_perm) {
	array<int, m> perm, best_perm, local_perm;
	int best_score = iinf;
	dforn(i, 0, m - 1) perm[i] = i;
	auto calc = [&](array<int, m>& perm) {
		return letter_map.greedy_calc(manager.perm_to_path(perm), sx, sy);
	};
	forn(tr, attempts) {
		ld tmp = init_tmp;
		//perm = PermutationAnnealing(manager, iter_count, 50, cooling);
		//shuffle(perm.begin(), perm.end(), gen);
		perm = init_perm;
		int local_best = calc(perm), current = local_best;
		local_perm = perm;
		forn(it, iter_count) {
			tmp *= cooling;
			vector<pii> story = move(perm, 3);
			int cand = calc(perm);
			if (cand < current) current = cand;
			else if (rand_rng(0, 1) < exp((current - cand) / tmp)) current = cand;
			else rollback(story, perm);
			if (current < local_best) local_best = current, local_perm = perm;
		}
		if (local_best < best_score) best_score = local_best, best_perm = local_perm;
	}
	return best_perm;
}

array<int, m> DjkstrAnnealing(Map& letter_map, WordsManager& manager, int sx, int sy, int attempts, int iter_count, ld init_tmp, ld cooling, function<vector<pii>(array<int, m>&, int)> move, array<int, m>& init_perm) {
	array<int, m> perm, best_perm, local_perm;
	int best_score = iinf;
	dforn(i, 0, m - 1) perm[i] = i;
	auto calc = [&](array<int, m>& perm) {
		return (letter_map.djkstr_calc(manager.perm_to_path(perm), sx, sy, false)).fst;
	};
	forn(tr, attempts) {
		ld tmp = init_tmp;
		//perm = PermutationAnnealing(manager, iter_count, 50, cooling);
		perm = init_perm;
		//shuffle(perm.begin(), perm.end(), gen);
		int local_best = calc(perm), current = local_best;
		local_perm = perm;
		forn(it, iter_count) {
			tmp *= cooling;
			vector<pii> story = move(perm, 10);
			int cand = calc(perm);
			if (cand < current) current = cand;
			else if (rand_rng(0, 1) < exp((current - cand) / tmp)) current = cand;
			else rollback(story, perm);
			if (current < local_best) local_best = current, local_perm = perm;
		}
		if (local_best < best_score) best_score = local_best, best_perm = local_perm;
	}
	return best_perm;
}

array<int, m> RandomDjkstrSearch(Map& letter_map, WordsManager& manager, int sx, int sy, int iter_count) {
	array<int, m> perm, best_perm;
	dforn(i, 0, m - 1) perm[i] = i;
	int best = iinf;
	auto calc = [&](array<int, m>& perm) {
		return (letter_map.djkstr_calc(manager.perm_to_path(perm), sx, sy, false)).fst;
	};
	forn(it, iter_count) {
		shuffle(perm.begin(), perm.end(), gen);
		int cand = calc(perm);
		if (cand < best) best = cand, best_perm = perm;
	}
	return best_perm;
}

array<int, m> RandomGreedySearch(Map& letter_map, WordsManager& manager, int sx, int sy, int iter_count) {
	array<int, m> perm, best_perm;
	dforn(i, 0, m - 1) perm[i] = i;
	int best = iinf;
	auto calc = [&](array<int, m>& perm) {
		return (letter_map.greedy_calc(manager.perm_to_path(perm), sx, sy));
	};
	forn(it, iter_count) {
		shuffle(perm.begin(), perm.end(), gen);
		int cand = calc(perm);
		if (cand < best) best = cand, best_perm = perm;
	}
	return best_perm;
}

void print_path(vector<pii> path) {
	aforn(v, path) cout << v.fst << " " << v.snd << '\n';
}
void skip_lines(int cnt) {
	forn(i, cnt) cout << '\n';
}
void init() {
	moves.push_back([&](array<int, m>& perm, int cnt) {
		vector<pii> story; vector<int> ind, nxt;
		dforn(i, 0, cnt - 1) ind.push_back(gen() % m);
		sort(ind.begin(), ind.end()); ind.erase(unique(ind.begin(), ind.end()), ind.end());
		dforn(i, 0, sz(ind) - 1) story.push_back({ ind[i], perm[ind[i]] }), nxt.push_back(perm[ind[i]]);
		shuffle(nxt.begin(), nxt.end(), gen);
		dforn(i, 0, sz(ind) - 1) perm[ind[i]] = nxt[i];
		return story;
		});
	moves.push_back([&](array<int, m>& perm, int cnt) {
		vector<pii> story; vector<int> ind, nxt;
		dforn(i, 0, cnt - 1) ind.push_back(gen() % m);
		sort(ind.begin(), ind.end()); ind.erase(unique(ind.begin(), ind.end()), ind.end());
		dforn(i, 0, sz(ind) - 1) story.push_back({ ind[i], perm[ind[i]] }), nxt.push_back(perm[ind[i]]);
		dforn(i, 0, sz(ind) - 1) perm[ind[i]] = nxt[(i + 1) % sz(ind)];
		return story;
		});
}

void solve() {
	int c, sx, sy; cin >> c >> c;
	cin >> sx >> sy;
	Map letter_map = input_map();
	WordsManager manager = input_words();
	init();
	array<int, m> res_perm = RandomGreedySearch(letter_map, manager, sx, sy, 25000);
	res_perm = GreedyAnnealing(letter_map, manager, sx, sy, 20, 20000, 2000, 0.999, moves[1], res_perm);
	print_path(letter_map.djkstr_calc(manager.perm_to_path(res_perm), sx, sy, true).snd);

	//skip_lines(3);
	//cout << result.fst << '\n';
}

int main()
{
	ios::sync_with_stdio(0); cin.tie(0); cout.tie(0);
	int t = 1;
	//cin >> t;
	while (t--) solve();
	return 0;
}