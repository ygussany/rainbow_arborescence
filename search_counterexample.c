/*
CC BY-NC
Written by Yutaro Yamaguchi, 2025-12-05.

Brute-force search with pruning for a counterexample for the rainbow arborescence conjecture:
For any set of (n - 1) spanning arborescences on the same n vertices, there exists a rainbow spanning arborescence.

[usage]
gcc -O3 search_counterexample.c -o search_counterexample.exe
search_counterexample.exe
n
(n should be given from the standard output and should be at most 10; o/w it immediately halts)
*/

int thres_memo = 25, thres_print = 8;
// Parameters defining thresholds for memoizing and printing
// The search branches of depth at most thres_memo are memoized for avoiding duplicated search for symmetric branches
// The search branches of depth at most thres_print are printed for checking the progress of DFS

/*
Vertices are indexed by the integers 1 through n.

Colors (= input arborescences/branchings) are also indexed by the integers 1 through n - 1.
The i-th color is specified by (n + 1) 4-bit integers A_par[i][0..n]:
A_par[i][0] is the vertex specified as the final root of color i.
For each vertex v,
A_par[i][v] = 0 if v is a (temporary) root;
A_par[i][v] is the parent of v (i.e., color i has an arc from color[i][v] to v) otherwise.

Each color A_par[i][0..n] is encoded into a 64-bit integer A[i] obtained by concatenating A_par[0..n] in this order, i.e., A[i] = the sum of A_par[i][v] * 2^(4(n-v)) (v = 0, 1, ..., n).
Then, a set of (n - 1) colors corresponds to an array of (n - 1) 64-bit integers A[1..(n-1)].
The canonical form of such an array A[1..(n-1)] is defined as follows:
- consider all isomorphic configurations A' (i.e., obtained from A by the permutation of the vertex indices [1..n]),
- sort each of them in the ascending order (i.e., A'[1] <= A'[2] <= ... <= A'[n-1]), and
- take the lexicographically smallest one among A'[1..(n-1)] obtained as above.

Each possible rainbow arborescence/branching (completed for the current set of colors) is specified by X_root[0..n]:
X_root[0] is an n-bit integer such that its i-th bit is 1 if and only if color i is already used.
X_root[v] is a 4-bit integer indicating the root of the arborescence containing vertex v.
(This information is sufficient instead of specifying which color is used for which vertex.)
Each possible rainbow branching X_root[0..n] is encoded into a 64-bit integer X obtained by concatenating X_root[0..n] in this order, i.e., X = the sum of X_root[v] * 2^(4(n-v)) (v = 0, 1, ..., n).
*/

#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>

struct timeval tt;
double tt_beg, tt_cur;

#define n_MAX 10
long long bit[61];

/* standard functions and data structures */

// sort x[1..n]
void merge_sort(int n, long long x[])
{
	static long long y[n_MAX + 1] = {};
	if (n <= 1) return;
	merge_sort(n / 2, x); // sort x[1..n/2]
	merge_sort(n - n / 2, &(x[n/2])); // sort x[(n/2+1)..n]
	
	int i, p, q;
	for (i = 1, p = 1, q = n / 2 + 1; i <= n; i++) {
		if (p > n / 2) y[i] = x[q++];
		else if (q > n) y[i] = x[p++];
		else y[i] = (x[p] <= x[q])? x[p++]: x[q++];
	}
	for (i = 1; i <= n; i++) x[i] = y[i];
}

// compare two arrays x[1..n] and y[1..n] in the lexicographic order
int is_lex_smaller_array(int n, long long x[], long long y[])
{
	int i;
	for (i = 1; i <= n; i++) {
		if (x[i] < y[i]) return 1; // x < y
		else if (x[i] > y[i]) return -1; // x > y
	}
	return 0; // x = y
}

// copy an array x[1..n] to y[1..n]
void copy_array(int n, long long x[], long long y[])
{
	int i;
	for (i = 1; i <= n; i++) y[i] = x[i];
}

// Find the lexicographic successor of p[1..n] on the same multiset (e.g., (3, 2, 4, 3, 3, 1) -> (3, 3, 1, 2 ,3, 4))
int next_permutation(int n, int p[])
{
	int i, j;
	for (i = n - 1; i >= 1; i--) if (p[i] < p[i+1]) break; // p[i] should be increased (p[(i+1)..n] is lexicographically maximum = non-increasing)
	if (i <= 0) return 0; // no successor (p[1..n] is lexicographically maximum)
	
	for (j = n; j > i; j--) if (p[j] > p[i]) break; // p[i] should be replaced by p[j]
	p[i] ^= p[j];
	p[j] ^= p[i];
	p[i] ^= p[j];
	for (i++, j = n; i < j; i++, j--) { // p[(i+1)..n] should be lexicographically minimum = non-decreasing
		p[i] ^= p[j];
		p[j] ^= p[i];
		p[i] ^= p[j];
	}
	return 1;
}

// Union-Find data structure
typedef struct {
	int par[n_MAX + 1], size[n_MAX + 1];
} UF_forest;

void UF_init(UF_forest *F, int n)
{
	int i;
	for (i = 1; i <= n; i++) {
		F->par[i] = i;
		F->size[i] = 1;
	}
}

int UF_root(UF_forest *F, int v)
{
	if (F->par[v] == v) return v;
	else {
		F->par[v] = UF_root(F, F->par[v]);
		return F->par[v];
	}
}

void UF_merge(UF_forest *F, int u, int v)
{
	u = UF_root(F, u);
	v = UF_root(F, v);
	if (u == v) return;
	else if (F->size[u] > F->size[v]) {
		F->par[v] = u;
		F->size[u] += F->size[v];
	} else {
		F->par[u] = v;
		F->size[v] += F->size[u];
	}
}


// hash table to maintain possible rainbow branchings
#define HASH 5000011
const int H_Mod = HASH;

#define nX_MAX 2000000

typedef struct HashListElement {
	struct HashListElement *next;
	long long X; // encoded rainbow branching
	char flag; // active (1) or inactive (0) or satisfying a sufficient condition (-1)
} hlist_ele;

typedef struct {
	int n;
	hlist_ele *hash[HASH], hd[nX_MAX];
} hash_table;

void init_hash_table(hash_table *H)
{
	int h;
	for (h = 0; h < H_Mod; h++) H->hash[h] = NULL;
	H->n = 0;
}

hlist_ele* find_hash_table(hash_table *H, long long X)
{
	int h = X % H_Mod;
	hlist_ele *hp;
	for (hp = H->hash[h]; hp != NULL; hp = hp->next) if (hp->X == X) break;
	return hp;
}

int add_hash_table(hash_table *H, long long X)
{
	int h;
	hlist_ele *hp = find_hash_table(H, X);
	if (hp != NULL) { // X is already in H
		if (hp->flag == 0) { // but X is inactive => activate
			hp->flag = 1;
			return -1;
		} else return 0;
	} else { // otherwise X is added to H
		h = X % H_Mod;
		H->hd[H->n].X = X;
		H->hd[H->n].flag = 1;
		H->hd[H->n].next = H->hash[h];
		H->hash[h] = &(H->hd[H->n++]);
		return 1;
	}
}


// hash table to maintain a set of (n - 1) colors (input branchings)
typedef struct HashListArrayElement {
	struct HashListArrayElement *next;
	long long A[n_MAX];
} hlist_array_ele;

#define nA_MAX 2000000

typedef struct {
	int n;
	hlist_array_ele *hash[HASH], hd[nA_MAX];
} hash_table_array;

int hash_func_array(int n, long long A[])
{
	int h = 0, i;
	for (i = 1; i < n; i++) h = ((h << 5) + A[i]) % H_Mod;
	return h;
}

void init_hash_table_array(hash_table_array *H)
{
	int h;
	for (h = 0; h < H_Mod; h++) H->hash[h] = NULL;
	H->n = 0;
}

hlist_array_ele* find_hash_table_array(hash_table_array *H, int n, long long A[])
{
	int h = hash_func_array(n, A);
	hlist_array_ele *hp;
	for (hp = H->hash[h]; hp != NULL; hp = hp->next) if (is_lex_smaller_array(n - 1, hp->A, A) == 0) break;
	return hp;
}

int add_hash_table_array(hash_table_array *H, int n, long long A[])
{
	int h;
	hlist_array_ele *hp = find_hash_table_array(H, n, A);
	if (hp != NULL) return 0; // A is already in H
	else { // otherwise A is added to H
		h = hash_func_array(n, A);
		copy_array(n - 1, A, H->hd[H->n].A);
		H->hd[H->n].next = H->hash[h];
		H->hash[h] = &(H->hd[H->n++]);
		return 1;
	}
}

/* ********** */

/* encode colors */

// A = the sum of A_par[v] * 2^(4*(n-v)) (v = 0, 1, ..., n)
long long encode_color(int n, int A_par[])
{
	int v;
	long long A = 0;
	for (v = 0; v <= n; v++) A = (A << 4) + A_par[v];
	return A;
}

// A[1..(n-1)] is the canonical form of A_par[1..(n-1)][0..n]
void make_canonical_form_colors(int n, int A_par[][n_MAX + 1], long long A[])
{
	int i;
	for (i = 1; i < n; i++) A[i] = encode_color(n, A_par[i]);
	merge_sort(n - 1, A);
	
	int j, v;
	static int p[n_MAX + 1], rho[n_MAX + 1], left[n_MAX + 1], right[n_MAX + 1], tmp_A_par[n_MAX][n_MAX + 1];
	long long tmp_A[n_MAX];
	for (v = 1, p[0] = 0; v <= n; v++) {
		p[v] = v;
		rho[v] = 0;
	}
	for (i = 1; i < n; i++) rho[A_par[i][0]]++; // rho[v] is the number of colors whose final roots are v
	for (j = n, v = 1; j >= 0; j--) { // the vertices in the interval [left[j], right[j]) are symmetric (in the terms of rho, i.e., rho[v] = j)
		left[j] = v;
		while (v <= n && rho[v] == j) v++;
		right[j] = v;
	}
	while (1) { // check all the possible permutations p[1..n] up to the symmetry in terms of rho
		for (j = 0; j <= n; j++) {
			if (next_permutation(right[j] - left[j], &(p[left[j] - 1])) != 0) break; // p[left[j]..right[j]] has the lexicographic successor, which should be updated
			for (v = left[j]; v < right[j]; v++) p[v] = v; // p[left[j]..right[j]] should be the lexicographically minimum = non-decreasing
		}
		if (j > n) break;
		
		for (i = 1; i < n; i++) {
			for (v = 1, tmp_A_par[i][0] = A_par[i][0]; v <= n; v++) tmp_A_par[i][p[v]] = p[A_par[i][v]]; // apply the permutation p[1..n] to the vertex indices
			tmp_A[i] = encode_color(n, tmp_A_par[i]);
		}
		merge_sort(n - 1, tmp_A);
		if (is_lex_smaller_array(n - 1, tmp_A, A) > 0) copy_array(n - 1, tmp_A, A); // tmp_A is lexicographically smaller than the current smallest A, which should be updated
	}
}

/* ********** */

/* encode/decode/edit/check rainbow branchings */

// X = the sum of X_root[v] * 2^(4*(n-v)) (v = 0, 1, ..., n)
long long encode_rainbow_branching(int n, int X_root[])
{
	int v;
	long long X = 0;
	for (v = 0; v <= n; v++) X = (X << 4) + X_root[v];
	return X;
}

void decode_rainbow_branching(int n, long long X, int X_root[])
{
	int i;
	for (i = n; i >= 1; i--, X >>= 4) X_root[i] = X & (bit[4] - 1);
	X_root[0] = X;
}

// get X_root[v] from X
int get_element_rainbow_branching(int n, long long X, int v)
{
	if (v == 0) return X >> (n * 4);
	else return (X >> ((n - v) * 4)) & (bit[4] - 1);
}

// edit X_root[v] of X into y
long long edit_element_rainbow_branching(int n, long long X, int v, int y)
{
	long long Y = X;
	if (v == 0) Y &= (bit[n*4] - 1);
	else Y &= (bit[n*5] - 1) ^ ((bit[4] - 1) << ((n - v) * 4));
	Y += (long long)y << ((n - v) * 4);
	return Y;
}


// Check whether X satisfies a sufficient condition for the existence of a rainbow spanning arborescence:
// It consists of exactly one nontrivial arborescence, which
// 1. contains all the multiroots (Theorem 4.2), or
// 2. uses all the colors having their roots outside (greedy).
int check_sufficiency_rainbow_arborescence(int n, int A_par[][n_MAX + 1], long long X)
{
	if (get_element_rainbow_branching(n, X, 0) == 0) return 0; // X is the trivial branching
	
	int v, k;
	static int X_root[n_MAX + 1], size[n_MAX + 1];
	decode_rainbow_branching(n, X, X_root);
	for (v = 1; v <= n; v++) size[v] = 0;
	for (v = 1; v <= n; v++) size[X_root[v]]++;
	for (v = 1, k = 0; v <= n; v++) if (size[v] >= 2) k++;
	if (k >= 2) return 0; // X consists of at least two nontrivial arborescences
	
	int i, r;
	static int rho[n_MAX + 1];
	for (v = 1; v <= n; v++) {
		rho[v] = 0;
		if (size[v] >= 2) r = v; // r is the root of the unique nontrivial arborescence in X
	}
	for (i = 1; i < n; i++) rho[A_par[i][0]]++;
	for (v = 1; v <= n; v++) if (rho[v] >= 2 && X_root[v] != r) break; // v is a multi-root but does not belong to the unique nontrivial arborescence
	if (v > n) return 1; // all the multi-roots are contained in the arborescence rooted at r

	for (i = 1; i < n; i++) if ((X_root[0] & bit[i]) == 0 && X_root[A_par[i][0]] != r) break; // color i is unused and has its root outside
	if (i >= n) return 1; // all the colors having their roots outside are used
	return 0;
}

// Compute a rainbow branching obtained from X by adding an arc of color i from u to v, which returns
// 0 if no new valid rainbow branching,
// -1 if a new valid rainbow branching implying a rainbow spanning arborescence, and
// Y if a new valid rainbow branching Y not immediately implying a rainbow spanning arborescence
long long grow_rainbow_branching(int n, int A_par[][n_MAX + 1], hash_table *H, long long X, int i, int u, int v)
{
	if ((get_element_rainbow_branching(n, X, 0) & bit[i]) != 0) return 0; // color i is already used in X
	if (get_element_rainbow_branching(n, X, v) != v) return 0; // vertex v already has an incoming arc in X
	if (get_element_rainbow_branching(n, X, u) == v) return 0; // u and v are in the same arborescence (rooted at v)
	
	int w;
	long long Y;
	static int Y_root[n_MAX + 1];
	decode_rainbow_branching(n, X, Y_root);
	Y_root[0] ^= bit[i]; // make color i used
	for (w = 1; w <= n; w++) if (Y_root[w] == v) Y_root[w] = Y_root[u]; // change the roots of vertices originally in the arborescence rooted at v
	Y = encode_rainbow_branching(n, Y_root);
	
	hlist_ele *hp = find_hash_table(H, Y);
	if (hp != NULL) { // Y has been computed so far
		if (hp->flag < 0) return -1; // Y implies a rainbow spanning arborescence
		else if (hp->flag > 0) return 0; // Y is already constructed in some other way
		else return Y;
	} else if (check_sufficiency_rainbow_arborescence(n, A_par, Y) != 0) { // Y implies a rainbow spanning arborescence
		add_hash_table(H, Y);
		hp = find_hash_table(H, Y);
		hp->flag = -1;
		return -1; 
	} else return Y;
}

/* ********** */

/* grow the set of colors */
// addible[i][u][v] maintains whether arc (u, v) of color i can be added without violating any constrains nor completing any rainbow spanning arborescences (> 0) or not (0),
// where its value reflects the number of newly completed rainbow branchings after adding the arc (not precisely counted)
// value[i][v] maintains the priority of pairs (i, v) to be chosen in the next DFS step (higher values are prioritized)

long long coeff_value[5];

// Update addible[i][1..n][1..n] (used just after some arc of color i is added)
void update_addible_flag_color(int n, int A_par[][n_MAX + 1], int addible[][n_MAX + 1][n_MAX + 1], long long value[][n_MAX + 1], int i)
{
	int u, v;
	static UF_forest F;
	UF_init(&F, n);
	for (u = 1; u <= n; u++) if (A_par[i][u] != 0) UF_merge(&F, u, A_par[i][u]); // maintain connected components of color i
	for (u = 1; u <= n; u++) {
		for (v = 1; v <= n; v++) {
			if (A_par[i][v] != 0 || UF_root(&F, u) == UF_root(&F, v)) { // v already has an incoming arc, or u and v belong to the same arborescence
				if (addible[i][u][v] > 0) {
					value[i][v] += coeff_value[0];
					if (u <= 3) value[i][v] -= coeff_value[3];
					if (v <= 3) value[i][v] -= coeff_value[3];
					value[i][v] -= addible[i][u][v] * coeff_value[4];
					addible[i][u][v] = 0;
				}
			}
		}
	}
}

// Grow colors in a DFS manner (depth = the total number of arcs currently fixed) 
void grow_colors(int n, int A_par[][n_MAX + 1], int depth)
{
	int i, u, v;
	static int addible[n_MAX][n_MAX + 1][n_MAX + 1], X_root[n_MAX + 1], q_head, q_tail;
	static long long q_X[nX_MAX], A[n_MAX], value[n_MAX][n_MAX + 1];
	static hash_table H_X;
	static hash_table_array H_A;
	if (depth == 0) { // initialization on the first call
		coeff_value[0] = bit[30]; // if addible[i][u][v] = 0, value[i][v] += coeff_value[0] (fewer choices are preferable)
		coeff_value[1] = bit[20]; // if A_par[i][u] = 0, value[i][v] += coeff_value[1] (sparser colors are preferable)
		coeff_value[2] = bit[20]; // if A_par[j][v] = 0, value[i][v] += coeff_value[2] (fewer incoming arcs are preferable)
		coeff_value[3] = bit[10]; // if addible[i][u][v] > 0 and u or v is a multi-root, value[i][v] += coeff_value[3] (multi-roots have some priority)
		coeff_value[4] = bit[0]; // if addible[i][u][v] > 0, value[i][v] += addible[i][u][v] * coeff_value[4] (more new rainbow branchings are preferable)
		for (i = 1; i < n; i++) for (v = 1; v <= n; v++) value[i][v] = coeff_value[1] * n + coeff_value[2] * (n - 1); // value[i][v] is a priority of choosing (i, v) in the next DFS step (larger values are prioritized)
		for (i = 1; i < n; i++) {
			for (u = 1; u <= n; u++) {
				for (v = 1; v <= n; v++) {
					if (A_par[i][0] == v || v == u) { // arc (u, v) of color i cannot be added by definition
						addible[i][u][v] = 0;
						value[i][v] += coeff_value[0];
					} else { // arc (u, v) of color i can be added and one new rainbow branching will be completed then
						addible[i][u][v] = 1;
						if (u <= 3) value[i][v] += coeff_value[3];
						if (v <= 3) value[i][v] += coeff_value[3];
						value[i][v] += coeff_value[4];
					}
				}
			}
		}
		
		init_hash_table_array(&H_A);
		init_hash_table(&H_X);
		for (v = 1, X_root[0] = 0; v <= n; v++) X_root[v] = v;
		q_tail = 0;
		q_X[++q_tail] = encode_rainbow_branching(n, X_root); // the trivial rainbow branching
		add_hash_table(&H_X, q_X[q_tail]);
	}
	if (depth <= thres_memo) { // memoize the canonical form of each completed branch of depth at most the prescribed threshold
		make_canonical_form_colors(n, A_par, A);
		if (find_hash_table_array(&H_A, n, A) != NULL) return; // one of the symmetric situations has already been completed
		add_hash_table_array(&H_A, n, A);
		if (depth <= thres_print) { // print the current branch if the search depth is at most the prescribed threshold
			for (i = 1; i < n; i++) { // colors
				for (v = 0; v <= n; v++) printf("%d ", A_par[i][v]);
				printf("\n");
			}
			printf("[%d] %d %d\n", H_A.n, depth, q_tail); // the number of distinct branches (memoized so far), the search depth, and the number of rainbow branchings completed in the current branch
		}
	}
	if (depth == (n - 1) * (n - 1)) { // counterexample (all the colors are completed but no rainbow spanning arborescence has been found)
		for (i = 1; i < n; i++) {
			for (v = 1; v <= n; v++) printf("%d ", A_par[i][v]);
			printf("\n");
		}
		printf("is a counterexample for the conjecture.\n");
		for (q_head = 1; q_head <= q_tail; q_head++) {
			decode_rainbow_branching(n, q_X[q_head], X_root);
			for (v = 0; v <= n; v++) printf("%d ", X_root[v]);
			printf("\n");
		}
		exit(0);
	}
	
	int argmax[2];
	long long max;
	for (i = 1, max = 0; i < n; i++) {
		for (v = 1; v <= n; v++) {
			if (A_par[i][0] != v && A_par[i][v] == 0 && max < value[i][v]) {
				max = value[i][v];
				argmax[0] = i;
				argmax[1] = v;
			}
		}
	}
	i = argmax[0];
	v = argmax[1];
	
	int ii, uu, vv;
	long long X, Y;
	static int tmp_q_tail[n_MAX * n_MAX], tmp_addible[n_MAX * n_MAX][n_MAX][n_MAX + 1][n_MAX + 1];
	static long long tmp_value[n_MAX * n_MAX][n_MAX][n_MAX + 1];
	hlist_ele *hp;
	for (u = 1; u <= n; u++) { // u is a candidate of the parent of v in color i
		if (addible[i][u][v] == 0) continue;
		
		A_par[i][v] = u;
		for (q_head = 1, tmp_q_tail[depth] = q_tail; q_head <= tmp_q_tail[depth]; q_head++) { // activate rainbow branchings newly completed by arc (u, v) of color i
			X = q_X[q_head];
			Y = grow_rainbow_branching(n, A_par, &H_X, X, i, u, v);
			if (Y < 0) break; // pruning (Y implies a rainbow spanning arborescence)
			else if (Y > 0) { // activate Y (newly completed)
				q_X[++q_tail] = Y;
				add_hash_table(&H_X, Y);
			}
		}
		if (q_head > tmp_q_tail[depth]) { // all the newly completed rainbow branchings are not sufficient, so DFS proceeds
			for (ii = 1; ii < n; ii++) { // remember the previous addible flags and evaluations
				for (uu = 1; uu <= n; uu++) for (vv = 1; vv <= n; vv++) tmp_addible[depth][ii][uu][vv] = addible[ii][uu][vv];
				for (vv = 1; vv <= n; vv++) tmp_value[depth][ii][vv] = value[ii][vv];
			}
			for (vv = 1; vv <= n; vv++) value[i][vv] -= coeff_value[1];
			for (ii = 1; ii < n; ii++) value[ii][v] -= coeff_value[2];
			update_addible_flag_color(n, A_par, addible, value, i); // update addible flags and evaluations according to the consistency of color i
			for (ii = 1; ii < n; ii++) { // update addible flags and evaluations by checking (symmetry and) rainbow branchings newly completed by arc (uu, vv) of color ii
				for (vv = 1; vv <= n; vv++) {
					if (A_par[ii][0] == vv || A_par[ii][vv] != 0) continue;
					for (uu = 1; uu <= n; uu++) {
						if (addible[ii][uu][vv] == 0) continue;
						A_par[ii][vv] = uu;
						/* checking symmetry here is heavy
						make_canonical_form_colors(n, A_par, A);
						if (find_hash_table_array(&H_A, n, A) != NULL) { // one of the symmetric situations has already been completed
							value[ii][vv] += coeff_value[0];
							if (uu <= 3) value[ii][vv] -= coeff_value[3];
							if (vv <= 3) value[ii][vv] -= coeff_value[3];
							value[ii][vv] -= addible[ii][uu][vv] * coeff_value[4];
							addible[ii][uu][vv] = 0;
						} else { */
							for (q_head = tmp_q_tail[depth] + 1; q_head <= q_tail; q_head++) {
								X = q_X[q_head];
								Y = grow_rainbow_branching(n, A_par, &H_X, X, ii, uu, vv);
								if (Y < 0) { // adding an arc (uu, vv) of color ii implies a rainbow spanning arborescence
									value[ii][vv] += coeff_value[0];
									if (uu <= 3) value[ii][vv] -= coeff_value[3];
									if (vv <= 3) value[ii][vv] -= coeff_value[3];
									value[ii][vv] -= addible[ii][uu][vv] * coeff_value[4];
									addible[ii][uu][vv] = 0;
									break;
								} else if (Y > 0) {
									addible[ii][uu][vv]++;
									value[ii][vv] += coeff_value[4];
								}
							}
						// }
						A_par[ii][vv] = 0;
					}
				}
			}
			grow_colors(n, A_par, depth + 1); // DFS proceeds
			for (ii = 1; ii < n; ii++) { // restore the previous addible flags and evaluations
				for (uu = 1; uu <= n; uu++) for (vv = 1; vv <= n; vv++) addible[ii][uu][vv] = tmp_addible[depth][ii][uu][vv];
				for (vv = 1; vv <= n; vv++) value[ii][vv] = tmp_value[depth][ii][vv];
			}
		}
		for (q_head = tmp_q_tail[depth] + 1; q_head <= q_tail; q_head++) { // inactivate the newly completed rainbow branchings
			Y = q_X[q_head];
			hp = find_hash_table(&H_X, Y);
			if (hp->flag > 0) hp->flag = 0;
		}
		A_par[i][v] = 0;
		q_tail = tmp_q_tail[depth];
	}
}

// Find the next root configuration in the lexicographic order:
// each root configuration is defined by rho[1-n] (rho[j] is the number of colors whose root is j), and
// rho is non-increasing (by symmetry) and rho[3] >= 2 (at least three multiroots are necessary).
int next_root_configuration(int n, int A_par[][n_MAX + 1])
{
	int i, j, k;
	static int rho[n_MAX + 1];
	for (j = 1; j <= n; j++) rho[j] = 0;
	for (i = 1; i < n; i++) rho[A_par[i][0]]++;
	for (j = n, k = 0; j > 3; j--) {
		if (rho[j] > 1) break;
		k += rho[j];
		rho[j] = 0;
	}
	if (j == 3) {
		for (; j >= 1; j--) {
			if (rho[j] > 2) break;
			k += rho[j];
			rho[j] = 0;
		}
		if (j == 0) return 0; // the input corresponds to rho = (2, 2, 2, 1, 1, ...), which is lexicographically minimum
	}
	rho[j]--;
	k++;
	for (j++; k > 0; j++) {
		rho[j] = (rho[j-1] <= k)? rho[j-1]: k;
		k -= rho[j];
		while (j == 2 && k < 2) { // we should keep rho[3] >= 2
			rho[j]--;
			k++;
		}
	}
	for (i = 1, j = 1; rho[j] > 0; j++) while (rho[j]--) A_par[i++][0] = j;
	return 1;
}

/* ********** */

int main()
{
	int i, v, n, A_par[n_MAX][n_MAX + 1];
	scanf("%d", &n);
	if (n > n_MAX || n < 7) return 0;

	// Initialization (the first root configuration is (1, 1, ..., 1, 2, 2, 3, 3))
	for (i = 1, bit[0] = 1; i <= 60; i++) bit[i] = bit[i-1] << 1;
	for (i = 1; i < n; i++) for (v = 0; v <= n; v++) A_par[i][v] = 0;
	for (i = 1; i < n - 4; i++) A_par[i][0] = 1;
	for (; i < n - 2; i++) A_par[i][0] = 2;
	for (; i < n; i++) A_par[i][0] = 3;

	gettimeofday(&tt, NULL);
	tt_beg = tt.tv_sec + (double)tt.tv_usec / 1000000;
	do {
		gettimeofday(&tt, NULL);
		tt_cur = tt.tv_sec + (double)tt.tv_usec / 1000000;
		fprintf(stderr, "[ ");
		for (i = 1; i < n; i++) fprintf(stderr, "%d ", A_par[i][0]);
		fprintf(stderr, "] starts (%.3f sec)\n", tt_cur - tt_beg);

		grow_colors(n, A_par, 0);
		
		gettimeofday(&tt, NULL);
		tt_cur = tt.tv_sec + (double)tt.tv_usec / 1000000;
		fprintf(stderr, "[ ");
		for (i = 1; i < n; i++) fprintf(stderr, "%d ", A_par[i][0]);
		fprintf(stderr, "] ends (%.3f sec)\n", tt_cur - tt_beg);
	} while (next_root_configuration(n, A_par));
	gettimeofday(&tt, NULL);
	tt_cur = tt.tv_sec + (double)tt.tv_usec / 1000000;
	return 0;
}