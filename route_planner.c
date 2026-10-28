/*
 * Smart Campus / City Route Planner  (C implementation)
 * Adjacency List + BFS reachability + Min-Heap Dijkstra + path reconstruction
 *
 * Build : gcc -O2 -std=c11 route_planner.c -o rp
 * Run   : ./rp              -> functional tests T1-T8
 *         ./rp bench        -> benchmark (heap vs linear scan, B1-B3)
 *         ./rp menu         -> interactive menu (Stage 1 functional requirements)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <limits.h>

#define NAMELEN 32
#define INF (LLONG_MAX / 4)

/* ---------------- Graph (Adjacency List) ---------------- */
typedef struct Edge { int to; int w; struct Edge *next; } Edge;

typedef struct {
    int n, cap;
    char (*name)[NAMELEN];
    Edge **head;
} Graph;

void graphInit(Graph *g) {
    g->n = 0; g->cap = 8;
    g->name = malloc(g->cap * sizeof *g->name);
    g->head = calloc(g->cap, sizeof *g->head);
}

void graphFree(Graph *g) {
    for (int i = 0; i < g->n; i++)
        for (Edge *e = g->head[i], *nx; e; e = nx) { nx = e->next; free(e); }
    free(g->name); free(g->head);
}

int findNode(const Graph *g, const char *s) {          /* -1 if absent */
    for (int i = 0; i < g->n; i++) if (strcmp(g->name[i], s) == 0) return i;
    return -1;
}

int addNode(Graph *g, const char *s) {                 /* create on first use */
    int id = findNode(g, s);
    if (id >= 0) return id;
    if (g->n == g->cap) {
        g->cap *= 2;
        g->name = realloc(g->name, g->cap * sizeof *g->name);
        g->head = realloc(g->head, g->cap * sizeof *g->head);
        memset(g->head + g->n, 0, (g->cap - g->n) * sizeof *g->head);
    }
    strncpy(g->name[g->n], s, NAMELEN - 1);
    g->name[g->n][NAMELEN - 1] = '\0';
    g->head[g->n] = NULL;
    return g->n++;
}

static void pushEdge(Graph *g, int u, int v, int w) {
    Edge *e = malloc(sizeof *e);
    e->to = v; e->w = w; e->next = g->head[u]; g->head[u] = e;
}

int addEdgeIdx(Graph *g, int u, int v, int w) {        /* symmetric insertion */
    pushEdge(g, u, v, w);
    pushEdge(g, v, u, w);
    return 1;
}

int addEdge(Graph *g, const char *a, const char *b, int w) {
    if (w < 0) {                                       /* FR2: reject negatives */
        printf("  [REJECTED] negative weight %d for %s - %s\n", w, a, b);
        return 0;
    }
    return addEdgeIdx(g, addNode(g, a), addNode(g, b), w);
}

static int dropOne(Graph *g, int u, int v) {
    for (Edge **p = &g->head[u]; *p; p = &(*p)->next)
        if ((*p)->to == v) { Edge *d = *p; *p = d->next; free(d); return 1; }
    return 0;
}

int removeEdge(Graph *g, const char *a, const char *b) {   /* Stage 1: deletion */
    int u = findNode(g, a), v = findNode(g, b);
    if (u < 0 || v < 0) return 0;
    int r = dropOne(g, u, v);
    if (u != v) dropOne(g, v, u);
    return r;
}

void printGraph(const Graph *g) {
    printf("Adjacency List (%d locations):\n", g->n);
    for (int i = 0; i < g->n; i++) {
        printf("  %-14s:", g->name[i]);
        if (!g->head[i]) printf(" (isolated)");
        for (Edge *e = g->head[i]; e; e = e->next)
            printf(" -> %s(%d)", g->name[e->to], e->w);
        printf("\n");
    }
}

/* ---------------- BFS reachability  O(V+E) ---------------- */
int bfsReachable(const Graph *g, int s, int t) {
    char *vis = calloc(g->n, 1);
    int *q = malloc(g->n * sizeof *q), qh = 0, qt = 0, found = 0;
    q[qt++] = s; vis[s] = 1;
    while (qh < qt) {
        int u = q[qh++];
        if (u == t) { found = 1; break; }
        for (Edge *e = g->head[u]; e; e = e->next)
            if (!vis[e->to]) { vis[e->to] = 1; q[qt++] = e->to; }
    }
    free(vis); free(q);
    return found;
}

/* ---------------- Min-Heap (binary, array based) ---------------- */
typedef struct { long long d; int v; } HNode;
typedef struct { HNode *a; int size, cap; } MinHeap;

void heapInit(MinHeap *h) { h->size = 0; h->cap = 16; h->a = malloc(h->cap * sizeof(HNode)); }
void heapFree(MinHeap *h) { free(h->a); }

void heapPush(MinHeap *h, long long d, int v) {        /* O(log V) */
    if (h->size == h->cap) { h->cap *= 2; h->a = realloc(h->a, h->cap * sizeof(HNode)); }
    int i = h->size++;
    while (i > 0) {
        int p = (i - 1) / 2;
        if (h->a[p].d <= d) break;
        h->a[i] = h->a[p]; i = p;
    }
    h->a[i].d = d; h->a[i].v = v;
}

HNode heapPop(MinHeap *h) {                            /* Extract-Min, O(log V) */
    HNode top = h->a[0], last = h->a[--h->size];
    int i = 0;
    while (2 * i + 1 < h->size) {
        int c = 2 * i + 1;
        if (c + 1 < h->size && h->a[c + 1].d < h->a[c].d) c++;
        if (h->a[c].d >= last.d) break;
        h->a[i] = h->a[c]; i = c;
    }
    if (h->size) h->a[i] = last;
    return top;
}

/* ---------------- Dijkstra with Min-Heap  O((V+E) log V) ---------------- */
/* returns distance, or -1 if unreachable; path[] gets plen nodes s..t */
long long dijkstra(const Graph *g, int s, int t, int *path, int *plen) {
    long long *dist = malloc(g->n * sizeof *dist);
    int *par = malloc(g->n * sizeof *par);
    for (int i = 0; i < g->n; i++) { dist[i] = INF; par[i] = -1; }
    MinHeap h; heapInit(&h);
    dist[s] = 0; heapPush(&h, 0, s);
    while (h.size) {
        HNode x = heapPop(&h);
        if (x.d > dist[x.v]) continue;                 /* stale entry */
        if (x.v == t) break;                           /* early exit */
        for (Edge *e = g->head[x.v]; e; e = e->next)
            if (dist[x.v] + e->w < dist[e->to]) {      /* relax only if smaller */
                dist[e->to] = dist[x.v] + e->w;
                par[e->to] = x.v;
                heapPush(&h, dist[e->to], e->to);      /* lazy insertion */
            }
    }
    long long res = dist[t] >= INF ? -1 : dist[t];
    *plen = 0;
    if (res >= 0) {
        int tmp[g->n > 0 ? g->n : 1], k = 0;
        for (int v = t; v != -1; v = par[v]) tmp[k++] = v;
        for (int i = k - 1; i >= 0; i--) path[(*plen)++] = tmp[i];
    }
    heapFree(&h); free(dist); free(par);
    return res;
}

/* ---------------- Linear-scan Dijkstra baseline  O(V^2) ---------------- */
long long dijkstraLinear(const Graph *g, int s, int t) {
    long long *dist = malloc(g->n * sizeof *dist);
    char *done = calloc(g->n, 1);
    for (int i = 0; i < g->n; i++) dist[i] = INF;
    dist[s] = 0;
    for (int i = 0; i < g->n; i++) {
        int u = -1;
        for (int v = 0; v < g->n; v++)
            if (!done[v] && (u == -1 || dist[v] < dist[u])) u = v;
        if (u == -1 || dist[u] >= INF) break;
        done[u] = 1;
        for (Edge *e = g->head[u]; e; e = e->next)
            if (dist[u] + e->w < dist[e->to]) dist[e->to] = dist[u] + e->w;
    }
    long long r = dist[t] >= INF ? -1 : dist[t];
    free(dist); free(done);
    return r;
}

/* ---------------- Query: validate -> BFS -> Dijkstra -> self-check ---------------- */
int query(const Graph *g, const char *a, const char *b, const char *label) {
    printf("%s: %s -> %s\n", label, a, b);
    int s = findNode(g, a), t = findNode(g, b);
    if (s < 0 || t < 0) { printf("  Invalid location name\n"); return 0; }
    int r = bfsReachable(g, s, t);
    printf("  BFS reachable: %s\n", r ? "YES" : "NO");
    if (!r) { printf("  No route available\n"); return 0; }

    int *path = malloc(g->n * sizeof *path), plen;
    long long d = dijkstra(g, s, t, path, &plen);
    printf("  Route: ");
    for (int i = 0; i < plen; i++) printf("%s%s", g->name[path[i]], i + 1 < plen ? " -> " : "");
    printf("\n  Total distance: %lld m\n", d);

    long long chk = 0; int ok = 1;                     /* edge-sum self-check */
    for (int i = 0; i + 1 < plen; i++) {
        int f = 0;
        for (Edge *e = g->head[path[i]]; e; e = e->next)
            if (e->to == path[i + 1]) { chk += e->w; f = 1; break; }
        ok = ok && f;
    }
    printf("  Edge-sum check: %lld m, consecutive edges exist: %s\n", chk, ok ? "YES" : "NO");
    free(path);
    return 1;
}

/* ---------------- Sample campus graph (Stage 3, Figure 2) ---------------- */
void buildCampus(Graph *g) {
    printf("== Building sample campus graph ==\n");
    addEdge(g, "Main Gate",   "Library",       120);
    addEdge(g, "Main Gate",   "Admin Block",    80);
    addEdge(g, "Admin Block", "Computer Lab",  100);
    addEdge(g, "Library",     "Computer Lab",  150);
    addEdge(g, "Library",     "Seminar Hall",   90);
    addEdge(g, "Computer Lab","Seminar Hall",   60);
    addNode(g, "Hostel");                              /* isolated node (T4) */
    addEdge(g, "Main Gate", "Cafeteria", -40);         /* invalid (T6) */
    printf("Vertices: %d\n\n", g->n);
}

void runTests(void) {
    Graph g; graphInit(&g);
    buildCampus(&g);
    printGraph(&g); printf("\n");
    query(&g, "Main Gate", "Library",      "T1 Direct route");
    query(&g, "Main Gate", "Computer Lab", "T2 Shortest route");
    query(&g, "Main Gate", "Seminar Hall", "T3 Reachability / T5 Path reconstruction");
    query(&g, "Main Gate", "Hostel",       "T4 Disconnected node");
    query(&g, "Main Gate", "Parking",      "T7 Invalid location name");
    query(&g, "Main Gate", "Main Gate",    "T8 Source equals destination");
    graphFree(&g);
}

/* ---------------- Benchmark B1-B3 ---------------- */
static unsigned long long rs = 42;
static unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }
static double ms(clock_t a, clock_t b) { return 1000.0 * (b - a) / CLOCKS_PER_SEC; }

void runBench(void) {
    int sizes[] = {1000, 5000, 20000};
    printf("V,E,heap_ms,linear_ms,dist_match\n");
    for (int z = 0; z < 3; z++) {
        int V = sizes[z]; Graph g; graphInit(&g); char nm[NAMELEN];
        for (int i = 0; i < V; i++) { sprintf(nm, "N%d", i); g.name[0][0] = 0;
            if (g.n == g.cap) { g.cap *= 2; g.name = realloc(g.name, g.cap * sizeof *g.name);
                g.head = realloc(g.head, g.cap * sizeof *g.head); }
            strcpy(g.name[g.n], nm); g.head[g.n++] = NULL; }
        for (int i = 1; i < V; i++) addEdgeIdx(&g, i, rnd() % i, 1 + rnd() % 100);   /* spanning tree */
        for (int k = 0; k < 2 * V; k++) addEdgeIdx(&g, rnd() % V, rnd() % V, 1 + rnd() % 100);
        long long E = 0;
        for (int i = 0; i < V; i++) for (Edge *e = g.head[i]; e; e = e->next) E++;
        E /= 2;
        int *p = malloc(V * sizeof *p), pl;
        clock_t t0 = clock(); long long d1 = dijkstra(&g, 0, V - 1, p, &pl);
        clock_t t1 = clock(); long long d2 = dijkstraLinear(&g, 0, V - 1);
        clock_t t2 = clock();
        printf("%d,%lld,%.3f,%.3f,%s\n", V, E, ms(t0, t1), ms(t1, t2), d1 == d2 ? "YES" : "NO");
        free(p); graphFree(&g);
    }
}

/* ---------------- Interactive menu (Stage 1 FR1-FR5) ---------------- */
static void readLine(const char *prompt, char *buf, int n) {
    printf("%s", prompt); fflush(stdout);
    if (!fgets(buf, n, stdin)) { buf[0] = 0; return; }
    buf[strcspn(buf, "\r\n")] = 0;
}

void runMenu(void) {
    Graph g; graphInit(&g);
    char a[64], b[64], w[32], c[16];
    for (;;) {
        printf("\n1.Add location/path  2.Remove path  3.Check reachability\n"
               "4.Shortest route     5.Show map     6.Load sample campus   0.Exit\n");
        readLine("Choice: ", c, sizeof c);
        int ch = atoi(c);
        if (ch == 0 && c[0] != '0') continue;
        if (ch == 0) break;
        if (ch == 1) {
            readLine("From: ", a, sizeof a); readLine("To: ", b, sizeof b);
            readLine("Distance (m): ", w, sizeof w);
            if (!a[0] || !b[0]) { printf("  Names cannot be empty\n"); continue; }
            if (addEdge(&g, a, b, atoi(w))) printf("  Path added.\n");
        } else if (ch == 2) {
            readLine("From: ", a, sizeof a); readLine("To: ", b, sizeof b);
            printf(removeEdge(&g, a, b) ? "  Path removed.\n" : "  No such path.\n");
        } else if (ch == 3 || ch == 4) {
            readLine("Source: ", a, sizeof a); readLine("Destination: ", b, sizeof b);
            if (ch == 4) query(&g, a, b, "Query");
            else {
                int s = findNode(&g, a), t = findNode(&g, b);
                if (s < 0 || t < 0) printf("  Invalid location name\n");
                else printf("  Reachable: %s\n", bfsReachable(&g, s, t) ? "YES" : "NO");
            }
        } else if (ch == 5) printGraph(&g);
        else if (ch == 6) buildCampus(&g);
    }
    graphFree(&g);
}

int main(int argc, char **argv) {
    if (argc > 1 && strcmp(argv[1], "bench") == 0) runBench();
    else if (argc > 1 && strcmp(argv[1], "menu") == 0) runMenu();
    else runTests();
    return 0;
}
