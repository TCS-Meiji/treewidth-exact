/* graph.h */
#ifndef NULL
#define NULL   ((void *) 0)
#endif

typedef struct vertex {
  int degree;
  int *neighbors;
} VERTEX;

typedef struct edge {
  int v1;
  int v2;
} EDGE;

typedef struct graph {
  int n;
  VERTEX* vertices;
} GRAPH;

int indexOf(int x, int a[], int n);
void addGraphEdge(GRAPH* graph, int u, int v);
int numberOfEdges(GRAPH* graph);
int numberOfDeg2Vertices(GRAPH* graph);
int theOtherNeighbor(int v, int aNeighbor, GRAPH* graph);
int theOtherEndOfChain(int w, GRAPH* graph, int parent[]);
int theOtherAttachmentOfChain(int v, int w, GRAPH* graph, int parent[]);

GRAPH* convert(GRAPH* graph, int n, int conv[], int inv[]);
GRAPH* convertWithEdge(GRAPH* graph, int n,int conv[], int inv[],
		       int cut1, int cut2);
GRAPH* contractChains(GRAPH* graph,
		      int n1, int parent[], int conv[]);

void dumpGraph(GRAPH* graph);
int markComponents(GRAPH* graph, int mark[]);
int markFrom(int v, GRAPH* graph, int mark[], int stack[]);
int markDeg2Chains(GRAPH* graph, int parent[]);
