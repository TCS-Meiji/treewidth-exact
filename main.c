#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include <time.h>
#include "graph.h"
#include "td.h"

/*#define VERBOSE*/
#define PRINT
/* #define MALLOC_TRACE */

struct timespec start;

typedef struct {
  int v1;
  int v2;
  int ic1;
  int ic2;
} CUT;

typedef struct {
  int size;
  int* vertices;
  int nCuts;
  CUT** cuts;
} COMPONENT;

TD* decompose(GRAPH* graph);
TD* decomposeBody(GRAPH* graph);
TD* decomposeConnected(GRAPH* graph1);
TD* decomposeMinDeg2(GRAPH* graph1);
TD* decomposeChainless(GRAPH* graph1);
int markTD(TD* td, int b, int v, int mark[]);
void printDecomposition(TD* td, int n);

int compare(const void *a, const void *b) {
  EDGE e = * (EDGE *) a;
  EDGE f = * (EDGE *) b;
  if (e.v1 < f.v1) return -1;
  else if (e.v1 > f.v1) return 1;
  else return e.v2 - f.v2;
}

GRAPH* readGraph() {
  char line[200];
  int n;
  int m;
  int u;
  int v;

  fgets(line,199, stdin);
  while (line[0] != 'p') {
    fgets(line, 199, stdin);
  }
  sscanf(line, "p tw %d %d", &n, &m);
#ifdef DEBUG
  printf("n = %d, m = %d\n", n, m);
#endif
  GRAPH* graph = malloc(sizeof(GRAPH));
  graph -> n = n;
  graph -> vertices = malloc(sizeof(VERTEX) * n); 

  EDGE* edges = malloc(sizeof(EDGE) * 2 * m);

  int i = 0;
  while (i < m) {
    fgets(line, 199, stdin);
    if (line[0] == 'c') {
      continue;
    }
    sscanf(line, "%d %d", &u, &v);
    //  printf("u = %d, v = %d\n", u, v);
    u--;
    v--;
    edges[2 * i].v1 = u;
    edges[2 * i].v2 = v;
    edges[2 * i + 1].v1 = v;
    edges[2 * i + 1].v2 = u;
    i++;
  }

  qsort(edges, 2 * m, sizeof(EDGE), compare);

  /* remove multiple edges and self loops */
  int m2 = 1;
  for (int i = 1; i < 2 * m; i++) {
    if ((edges[i - 1].v1 != edges[i].v1 || 
        edges[i - 1].v2 != edges[i].v2) &&
        edges[i].v1 != edges[i].v2) {
      edges[m2++] = edges[i];
    }
  }

  int *p = (int *) edges;
  int k = 0;
  for (int i = 0; i < n; i++) {
    graph->vertices[i].neighbors = &p[k];
    int deg = 0;
    while (edges[k].v1 == i && k < m2) {
      deg++;
      p[k] = edges[k].v2;
      k++;
    }
    graph->vertices[i].degree = deg;
  }

  for (int i = 0; i < graph->n; i++) {
    int* neighbors = 
      malloc(sizeof(int) * graph->vertices[i].degree);
    for (int j = 0; j < graph->vertices[i].degree; j++) {
      neighbors[j] = graph->vertices[i].neighbors[j];
    }
    graph->vertices[i].neighbors = neighbors;
  }

  free(edges);

  return graph;
  //  printf("returning %d\n", nRead);
}

int* invertBag(BAG bag, int inv[]) {
  int* vertices = malloc(sizeof(int) * bag.nv);
  for (int i = 0; i < bag.nv; i++) {
    vertices[i] = inv[bag.vertices[i]];
  } 
  return vertices;
}

int bagContains(BAG bag, int v) {
  for (int i = 0; i < bag.nv; i++) {
    if (bag.vertices[i] == v) {
      return 1;
    }
  }
  return 0;
}

int findBag(TD* td, int v) {
  for (int b = 0; b < td->nBag; b++) {
    if (bagContains(td->bags[b], v)) {
      return b;
    }
  }
  return -1;
}

int findBagBetween(TD* td, int v, int b1, int b2) {
  for (int b = b1; b < b2; b++) {
    if (bagContains(td->bags[b], v)) {
      return b;
    }
  }
  return -1;
}

int findBag2(TD* td, int u, int v) {
  for (int b = 0; b < td->nBag; b++) {
    if (bagContains(td->bags[b], u) &&
        bagContains(td->bags[b], v)) {
      return b;
    }
  }
  return -1;
}

int findBag2Between(TD* td, int u, int v, int b1, int b2) {
  for (int b = b1; b < b2; b++) {
    if (bagContains(td->bags[b], u) &&
        bagContains(td->bags[b], v)) {
      return b;
    }
  }
  return -1;
}

int tdContainsVertex(TD* td, int v) {
  for (int b = 0; b < td->nBag; b++) {
    if (bagContains(td->bags[b], v)) {
      return 1;
    }
  }
  return 0;
}

int tdContainsEdge(TD* td, int u, int v) {
  for (int b = 0; b < td->nBag; b++) {
    if (bagContains(td->bags[b], u) &&
        bagContains(td->bags[b], v)) {
      return 1;
    }
  }
  return 0;
}

int countBagsWith(TD* td, int v) {
  int count = 0;
  for (int b = 0; b < td->nBag; b++) {
    if (bagContains(td->bags[b], v)) {
      count++;
    }
  }
  return count;
}

int markTD(TD* td, int b, int v, int mark[]) {
  if (mark[b]) {
    return 0;
  }
  int k = 1;
  mark[b] = 1;
  for (int i = 0; i < td->nEdge; i++) {
    int b3 = -1;
    if (td->edges[i].b1 == b)
      b3 = td->edges[i].b2;
    else if (td->edges[i].b2 == b) {
      b3 = td->edges[i].b1; 
    }
    if (b3 >= 0 && bagContains(td->bags[b3], v)) {
      k += markTD(td, b3, v, mark);
    }
  }
  return k;
}

int formsTree(TD* td, int v) {
  int k1 = countBagsWith(td, v);
  int b0 = findBag(td, v);
  int mark[td->nBag];
  for (int i = 0; i < td->nBag; i++) {
    mark[i] = 0;
  }
  int k2 = markTD(td, b0, v, mark);
  /*  printf("%d, %d, %d\n", v + 1, k1, k2);*/
  return k1 == k2;
}

int validate(TD* td, GRAPH* graph) {
  for (int b = 0; b < td->nBag; b++) {
    if (td->bags[b].nv == 0) {
      fprintf(stderr, "empty bag %d, nbag = %d, n = %d\n", 
          b, td->nBag, graph-> n);
    }
  }

  for (int v = 0; v < graph->n; v++) {
    if (!tdContainsVertex(td, v)) {
      fprintf(stderr, "vertex %d missing", v + 1);
      return 0;
    }
  }
  for (int v = 0; v < graph->n; v++) {
    for (int i = 0; i < graph->vertices[v].degree; i++) {
      int w = graph->vertices[v].neighbors[i];
      if (!tdContainsEdge(td, v, w)) {
        fprintf(stderr, "edge (%d,%d) missing", v + 1, w + 1);
        return 0;
      }
    }
  }
  for (int v = 0; v < graph->n; v++) {
    if (!formsTree(td, v)) {
      fprintf(stderr, "bags with %d not connected", v + 1);
      return 0;
    }
  }
  for (int b = 0; b < td->nBag; b++) {
    if (td->bags[b].nv > td->width + 1) {
      fprintf(stderr, "bag size exceeds width + 1\n");
      return 0;
    }
  }
  return 1;
}

void freeTD(TD* td) {
  int n = td->nBag;
  for (int b = td->nBag - 1; b >= 0; b--) {
    /*    printf("freeing vertieces %p\n", td->bags[b].vertices);*/
    free(td->bags[b].vertices);
  }
  if (td->nEdge != 0) {
/*    printf("freeing edges %p\n", td->edges);*/
    free(td->edges);
  }
/*  printf("freeing bags %p\n", td->bags);*/
  free(td->bags);
/*  printf("freeing td %p\n", td);*/
  free(td);
}

void freeGraph(GRAPH* graph) {
  for (int v = graph->n - 1; v >= 0; v--) {
    /*    printf("freeing neighbors %p\n", graph->vertices[v].neighbors);*/
    free(graph->vertices[v].neighbors);
  }
/*   printf("freeing vertices %p\n", graph->vertices);*/
  free(graph->vertices);
/*   printf("freeing graph %p\n", graph);*/
  free(graph);
}

TD* zeroBagTree(GRAPH* graph) {
  TD* td = malloc(sizeof(TD));
  td->nBag = 0;
  td->nEdge = 0;
  td->width = -1;
  return td;
}

TD* oneBagTree(GRAPH* graph) {
  TD* td = malloc(sizeof(TD));
  td->nBag = 1;
  td->nEdge = 0;
  td->width = graph->n - 1;
  td->bags = malloc(sizeof(BAG));
  td->bags[0].nv = graph->n;
  td->bags[0].vertices = malloc(sizeof(int)*graph->n);
  for (int v = 0; v < graph-> n; v++){
    td->bags[0].vertices[v] = v;
  }
  return td;
}


int markAttachedTrees(GRAPH* graph, int parent[]) {
  int moving = 1;
  int k = 0;
  while (moving) {
    moving = 0;
    for (int v = 0; v < graph->n; v++) {
      if (parent[v] >= 0) continue;
      int count = 0;
      int p;
      VERTEX vertex = graph->vertices[v];
      for (int i = 0; i < vertex.degree; i++) {
        int w = vertex.neighbors[i];
        if (parent[w] == v) {
          count++;
        }
        else {
          p = w;
        }
      }
      if (vertex.degree - count == 1) {
        parent[v] = p;
        k++;
        moving = 1;
      }
    }
  }
  return k;
}

BAG bag2(int u, int v) {
  BAG bag;
  bag.nv = 2;
  bag.vertices = malloc(sizeof(int) * 2);
  bag.vertices[0] = u;
  bag.vertices[1] = v;
  return bag;
}

BAG bag3(int u, int v, int w) {
  BAG bag;
  bag.nv = 3;
  bag.vertices = malloc(sizeof(int) * 3);
  bag.vertices[0] = u;
  bag.vertices[1] = v;
  bag.vertices[2] = w;
  return bag;
}

TD* decomposeCycle(GRAPH* graph) {
#ifdef VERBOSE
  printf("decomposeCycle: n = %d\n", graph->n);
#endif
  TD* td = malloc(sizeof(TD));
  int n = graph->n;
  td->nBag = n - 2;
  td->nEdge = n - 3;
  td->width = 2;
  td->bags = malloc(sizeof(BAG) * (n -2));
  td->edges = malloc(sizeof(TDEDGE) * (n - 3));
  int current = graph->vertices[0].neighbors[0];
  int next = theOtherNeighbor(current, 0, graph);
  for (int b = 0; b < n - 2; b++) {
    td->bags[b] = bag3(0, current, next);
    if (b > 0) {
      td->edges[b-1].b1 = b - 1;
      td->edges[b-1].b2 = b;
    }
    int newNext = theOtherNeighbor(next, current, graph);
    current = next;
    next = newNext;
  }
  return td;
}

int attachBagsForChain(int s, int t, GRAPH* graph,
    TD* td, int parent[], int nb, int ne) {
  int v0 = theOtherNeighbor(s, parent[s], graph);
  int v1 = parent[t];
  int b = findBag2(td, v0, v1);
  td->bags[nb] = bag3(v1, v0, s);
  td->edges[ne].b1 = b;
  td->edges[ne].b2 = nb;

  int current = s;
  int i = 1;
  while (current != t) {
    td->bags[nb + i] = bag3(v1, current, parent[current]);
    td->edges[ne + i].b1 = nb + i - 1;
    td->edges[ne + i].b2 = nb + i;
    i++;
    current = parent[current];
  }
  return i;
}

TD* decomposeMinDeg2(GRAPH* graph) {
#ifdef VERBOSE
  printf("decomposeMinDeg2: n = %d\n", graph->n);
#endif

  if (graph->n <= 3) {
    return oneBagTree(graph);
  }

  if (graph->n == numberOfEdges(graph)) {
    return decomposeCycle(graph);
  }
  int n = graph->n;
  int parent[n];
  for (int i = 0; i < n; i++) {
    parent[i] = -1;
  }


  int k = markDeg2Chains(graph, parent);

  /* int k1 = numberOfDeg2Vertices(graph);
  printf("k = %d, k1 = %d\n", k, k1);				
   */

  if (k == 0) {
    return decomposeChainless(graph);
  }

  int conv[n];
  int inv[n - k];

  int j = 0;
  for (int v = 0; v < n; v++) {
    if (parent[v] == -1) {
      conv[v] = j;
      inv[j++] = v;
    }
    else {
      conv[v] = -1;
    }
  }
  GRAPH* graph1 = contractChains(graph, n - k, parent, conv);

  TD* td1 = decomposeChainless(graph1);

  /*
  printDecomposition(td1, n - k);
   */
  TD* td = malloc(sizeof(TD));
  td->nBag = td1->nBag + k;
  td->nEdge = td1->nEdge + k;
  td->width = td1->width;
  if (td1->width <= 1) {
    td->width = 2;
  }

  td->bags = malloc(sizeof(BAG) * td->nBag);
  td->edges = malloc(sizeof(TDEDGE) * td->nEdge);

  int nb = td1->nBag;

  int ne = td1->nEdge;

  for (int b = 0; b < nb; b++) {
    td->bags[b].nv = td1->bags[b].nv;
    td->bags[b].vertices = invertBag(td1->bags[b], inv);
  }
  for (int i = 0; i < ne; i++) {
    td->edges[i] = td1->edges[i];
  }

  for (int v = 0; v < n; v++) {
    VERTEX vertex = graph->vertices[v];
    if (parent[v] >= 0) continue;
    for (int i = 0; i < vertex.degree; i++) {
      int w = vertex.neighbors[i];
      if (parent[w] == v) {
        int z = theOtherEndOfChain(w, graph, parent);
        int s = attachBagsForChain(z, w, graph, td, parent, nb, ne);
        int s1 = 0;
        int y = z;
        while (parent[y] >= 0) {
          s1++;
          y = parent[y];
        }
        nb += s;
        ne += s;
      }
    }
  }

  if (nb != td->nBag) {
    fprintf(stderr, "%d inconsistent with bag number %d\n", nb, td->nBag);
    exit(1);
  }
  if (ne != td->nEdge) {
    fprintf(stderr, "%d inconsistent with edge number %d\n", ne, td->nEdge);
    exit(1);
  }
#ifdef VERBOSE
  printf("decomposeMinDeg2 returning: n = %d\n", graph->n);
#endif
  return td;
}

int attachBagsForTree(int b, int r, GRAPH* graph,
    TD* td, int parent[], int nb, int ne) {
  td->bags[nb] = bag2(parent[r], r);
  td->edges[ne].b1 = b;
  td->edges[ne].b2 = nb;
  int i = 1;
  VERTEX vertex = graph->vertices[r];
  for (int j = 0; j < vertex.degree; j++) {
    int v = vertex.neighbors[j];
    if (v == parent[r]) {
      continue;
    }
    int s = attachBagsForTree(nb, v, graph, td, parent, nb + i, ne + i);
    i += s;
  }
  return i;
}

TD* decomposeConnected(GRAPH* graph) {
#ifdef VERBOSE
  printf("decomposeConnected: n = %d\n", graph->n);
#endif

  int n = graph->n;

  if (n <= 2) {
    return oneBagTree(graph);
  }

  int parent[n];
  for (int i = 0; i < n; i++) {
    parent[i] = -1;
  }
  int k = markAttachedTrees(graph, parent);

  if (k == 0) {
    return decomposeMinDeg2(graph);
  }

  int conv[n];
  int inv[n - k];

  int j = 0;
  for (int v = 0; v < n; v++) {
    if (parent[v] == -1) {
      conv[v] = j;
      inv[j++] = v;
    }
    else {
      conv[v] = -1;
    }
  }

  GRAPH* graph1 = convert(graph, n - k, conv, inv);
  /*  dumpGraph(graph1); */
  TD* td1 = decomposeMinDeg2(graph1);

  TD* td = malloc(sizeof(TD));
  td->nBag = td1->nBag + k;
  td->nEdge = td1->nEdge + k;
  if (td1->width == 0) {
    td->width = 1;
  }
  else {
    td->width = td1->width;
  }
  td->bags = malloc(sizeof(BAG) * td->nBag);
  td->edges = malloc(sizeof(TDEDGE) * td->nEdge);

  int nb = td1->nBag;
  int ne = td1->nEdge;

  for (int b = 0; b < nb; b++) {
    td->bags[b].nv = td1->bags[b].nv;
    td->bags[b].vertices = invertBag(td1->bags[b], inv);
  }
  for (int i = 0; i < ne; i++) {
    td->edges[i] = td1->edges[i];
  }

  for (int v = 0; v < n; v++) {
    if (parent[v] >= 0 && parent[parent[v]] == -1) {
      int b = findBag(td, parent[v]);
      int s = attachBagsForTree(b, v, graph, td, parent, nb, ne);
      nb += s;
      ne += s;
    }
  }
#ifdef VERBOSE
  printf("decomposeConnected returning: n = %d, width = %d\n", 
      graph->n, td->width);
#endif
  return td;
}

TD* decompose(GRAPH* graph) {
  int n = graph->n;
#ifdef VERBOSE
  printf("decompose: n = %d\n", n);
#endif

  if (n == 0) {
    return zeroBagTree(graph);
  }

  int mark[n];
  for (int i = 0; i < n; i++) {
    mark[i] = -1;
  }
  int nc = markComponents(graph, mark);
  if (nc == 1) {
    TD* td = decomposeConnected(graph);
#ifdef VERBOSE
    printf("decompose returning: n = %d, width = %d\n", n, td->width);
#endif
    return td;
  }

  int conv[n];
  int invAll[n];
  int cSize[nc];
  for (int c = 0; c < nc; c++) {
    cSize[c] = 0;
  } 

  for (int v = 0; v < n; v++) {
    conv[v] = cSize[mark[v]]++;
  }

  int invOffset[nc];
  invOffset[0] = 0;
  for (int c = 1; c < nc; c++) {
    invOffset[c] = invOffset[c - 1] + cSize[c - 1];
  }

  for (int v = 0; v < n; v++) {
    int w = conv[v];
    int c = mark[v];
    invAll[invOffset[c] + w] = v;
  }

  TD* td = malloc(sizeof(TD));
  td->bags = malloc(sizeof(BAG) * n * 2);
  td->edges = malloc(sizeof(TDEDGE) * n * 2);
  td->width = 0;

  int nb = 0;
  int ne = 0;

  for (int c = 0; c < nc; c++) {
    int inv[cSize[c]];
    for (int w = 0; w < cSize[c]; w++) {
      inv[w] = invAll[invOffset[c] + w];
    }
    GRAPH* graph1 = convert(graph, cSize[c], conv, inv);
    TD* td1 = decomposeConnected(graph1);
    if (td1->width > td->width) {
      td->width = td1->width;
    }
    for (int b = 0; b < td1->nBag; b++) {
      td->bags[nb + b].nv = td1->bags[b].nv;
      td->bags[nb + b].vertices = invertBag(td1->bags[b], inv); 
    }
    for (int i = 0; i < td1->nEdge; i++) {
      td->edges[ne + i].b1 = td1->edges[i].b1 + nb;
      td->edges[ne + i].b2 = td1->edges[i].b2 + nb;
    }
    int nb1 = nb + td1->nBag;
    int ne1 = ne + td1->nEdge;
    if (c < nc - 1) {
      td->edges[ne1].b1 = nb;
      td->edges[ne1].b2 = nb1;
      ne1++;
    }
    nb = nb1;
    ne = ne1;
    freeTD(td1);
    freeGraph(graph1);
  }
  td->nBag = nb;
  td->nEdge = ne;
#ifdef VERBOSE
  printf("decompose returning: n = %d, width = %d\n", graph->n, td->width);
#endif

  return td;
}

void addCut(COMPONENT* compo, CUT* cut) {
  if (compo->nCuts == compo->size * 3) {
    fprintf(stderr, "too many cuts for a component\n");
    exit(1);
  }
  compo->cuts[compo->nCuts++] = cut;
}
	
void checkCutOwner(CUT* cut, COMPONENT c) {
  for (int i = 0; i < c.nCuts; i++) {
    if (c.cuts[i] == cut) return;
  }
  fprintf(stderr, "cut %d, %d (%d:%d) not found in component of size %d\n",
	  cut->v1, cut->v2, cut->ic1, cut->ic2, c.size);
}

void checkCuts(COMPONENT c, GRAPH* graph) {
  for (int i = 0; i < c.nCuts; i++) {
    if (indexOf(c.cuts[i]->v1, c.vertices, c.size) < 0) {
      fprintf(stderr, "cut vertex %d not in component of size %d\n", 
	      c.cuts[i]->v1, c.size);
      exit(1);
    }
    if (c.cuts[i]->v2 >= 0 && 
	indexOf(c.cuts[i]->v2, c.vertices, c.size) < 0) {
      fprintf(stderr, "2nd cut vertex %d not in component of size %d\n", 
	      c.cuts[i]->v2, c.size);
      exit(1);
    }
    /*
    printf("checking cut no.%d, v1 = %d, v2 = %d\n", i, c.cuts[i]->v1, c.cuts[i]->v2);
    */
    if (c.cuts[i]->v2 >= 0 && 
	indexOf(c.cuts[i]->v2, graph->vertices[c.cuts[i]->v1].neighbors, 
			     graph->vertices[c.cuts[i]->v1].degree) < 0) {
      fprintf(stderr, "the edge for the two vertex cut (%d, %d) not found\n", 
	      c.cuts[i]->v1, c.cuts[i]->v2);
      exit(1);
    }
  }
  /*
  printf("cuts ok with a comopnent of size %d\n", c.size);
  */
}

TD* decomposeChainless(GRAPH* graph) {
  /* This decomposition procedure is destructive:
   * when we find a 2 vertex cut, we add an edge to the original graph.
   * This does not change the treewidth, but the caller of this procedure
   * must be aware of it.
   */

  int n = graph->n;
#ifdef VERBOSE
  printf("decomposeChainless: n = %d\n", n);
#endif

  int mark[n];
  int stack[numberOfEdges(graph) * 2];

  COMPONENT components[n];
  CUT cuts[n];
  int nCompo = 1;
  int nCuts = 0;
  components[0].size = n;
  components[0].vertices = malloc(sizeof(int) * n);
  components[0].nCuts = 0;
  components[0].cuts = malloc(sizeof(CUT*) * n * 3);

  for (int v = 0; v < n; v++) {
    components[0].vertices[v] = v;
  }

  int ic = 0;
  
  while (ic < nCompo) {
    int s = components[ic].size;
    if (s <= 2) {
      ic++;
      continue;
    }
    int stay = 0;
    for (int v = 0; v < n; v++) {
      mark[v] = -1;
    } 

    if (components[ic].nCuts > 0) {
      /* this "component" may possibly be disconnected because of the
         last cut: deal with this possibility  */
      CUT* cut0 = components[ic].cuts[components[ic].nCuts - 1];
      for (int i = 0; i < s; i++) {
        int v = components[ic].vertices[i];
        mark[v] = 0;
      }
      mark[cut0->v1] = -1;

      int n1;
      if (cut0->v1 != components[ic].vertices[0]) {
        n1 = markFrom(components[ic].vertices[0], graph, mark, stack);
      }
      else {
        n1 = markFrom(components[ic].vertices[1], graph, mark, stack);
      }
      if (n1 < s - 1) {
#ifdef VERBOSE
	printf("split1 (with an existing cut) %d -> %d, %d\n", s, n1 + 1, s - n1);
#endif
        components[ic].size = n1 + 1;
        int* vertices = malloc(sizeof(int) * (s - n1));
        int j = 0;
        int k = 0;
        for (int i = 0; i < s; i++) {
          int v = components[ic].vertices[i];
          if (v == cut0->v1) {
            components[ic].vertices[j++] = v;
            vertices[k++] = v;
          }
          else if (mark[v]) {
            components[ic].vertices[j++] = v;
          }
          else {
            vertices[k++] = v;
          }
        }
        if (nCuts == n) {
          fprintf(stderr, "too many cuts\n");
          exit(1);
        }
        if (nCompo == n) {
          fprintf(stderr, "too many components\n");
          exit(1);
        }
        components[nCompo].size = s - n1;
        components[nCompo].vertices = vertices;
        components[nCompo].nCuts = 0;
        components[nCompo].cuts = malloc(sizeof(CUT*) * (s - n1) * 3);

        j = 0;
        for (int i = 0; i < components[ic].nCuts; i++) {
          CUT* cut = components[ic].cuts[i];
          if (indexOf(cut->v1, components[ic].vertices, components[ic].size)
              >= 0) {
            components[ic].cuts[j++] = cut;
          }
          else {
            addCut(&components[nCompo], cut);
	    if (cut->ic1 == ic) cut->ic1 = nCompo;
	    else if (cut->ic2 == ic) cut->ic2 = nCompo;
	    else {
	      fprintf(stderr, "cut inconsistency\n");
	      exit(1);
	    }
          }
        }
        components[ic].nCuts = j;

        addCut(&components[ic], &cuts[nCuts]);
        addCut(&components[nCompo], &cuts[nCuts]);

        cuts[nCuts].v1 = cut0->v1;
        cuts[nCuts].v2 = -1;
        cuts[nCuts].ic1 = ic;
        cuts[nCuts].ic2 = nCompo;
        nCuts++;
        nCompo++;

        continue;
      }
    }

    for (int vc = 0; vc < s; vc++) {
      for (int i = 0; i < s; i++) {
        int v = components[ic].vertices[i];
        mark[v] = 0;
	if (i == vc) {
	    mark[v] = -1;
	  }
      }

      int n1;
      if (vc != 0) {
        n1 = markFrom(components[ic].vertices[0], graph, mark, stack);
      }
      else {
        n1 = markFrom(components[ic].vertices[1], graph, mark, stack);
      }
      if (n1 < s - 1) {
#ifdef VERBOSE
	printf("split1 %d -> %d, %d\n", s, n1 + 1, s - n1);
#endif
	int theCut = components[ic].vertices[vc];

        components[ic].size = n1 + 1;
        int* vertices = malloc(sizeof(int) * (s - n1));
        int j = 0;
        int k = 0;
        for (int i = 0; i < s; i++) {
          int v = components[ic].vertices[i];
          if (i == vc) {
            components[ic].vertices[j++] = v;
            vertices[k++] = v;
          }
          else if (mark[v]) {
            components[ic].vertices[j++] = v;
          }
          else {
            vertices[k++] = v;
          }
        }
        if (nCuts == n) {
          fprintf(stderr, "too many cuts\n");
          exit(1);
        }
        if (nCompo == n) {
          fprintf(stderr, "too many components\n");
          exit(1);
        }
        components[nCompo].size = s - n1;
        components[nCompo].vertices = vertices;
        components[nCompo].nCuts = 0;
        components[nCompo].cuts = malloc(sizeof(CUT*) * (s - n1) * 3);

        j = 0;
        for (int i = 0; i < components[ic].nCuts; i++) {
          CUT* cut = components[ic].cuts[i];
          if (indexOf(cut->v1, components[ic].vertices, components[ic].size)
              >= 0) {
            components[ic].cuts[j++] = cut;
          }
          else {
            addCut(&components[nCompo], cut);
	    if (cut->ic1 == ic) cut->ic1 = nCompo;
	    else if (cut->ic2 == ic) cut->ic2 = nCompo;
	    else {
	      fprintf(stderr, "cut inconsistency\n");
	      exit(1);
	    }
          }
        }

        components[ic].nCuts = j;

        addCut(&components[ic], &cuts[nCuts]);
        addCut(&components[nCompo], &cuts[nCuts]);

        cuts[nCuts].v1 = theCut;
        cuts[nCuts].v2 = -1;
        cuts[nCuts].ic1 = ic;
        cuts[nCuts].ic2 = nCompo;
        nCuts++;
        nCompo++;
	stay = 1;
        break;
      }
    }
    if (!stay) ic++;
  }

  ic = 0;
  while (ic < nCompo) {
    int s = components[ic].size;
    if (s <= 3) {
      ic++;
      continue;
    }
    for (int v = 0; v < n; v++) {
      mark[v] = -1;
    } 

    if (components[ic].nCuts > 0) {
      /* this "component" may possibly be disconnected because of the
	 last cut: deal with this possibility  */

      CUT* cut0 = components[ic].cuts[components[ic].nCuts - 1];
      for (int i = 0; i < s; i++) {
        int v = components[ic].vertices[i];
        mark[v] = 0;
      }
      mark[cut0->v1] = -1;
      mark[cut0->v2] = -1;
      int n1;
      if (cut0->v1 != components[ic].vertices[0] &&
          cut0->v2 != components[ic].vertices[0]) {
        n1 = markFrom(components[ic].vertices[0], graph, mark, stack);
      }
      else if (cut0->v1 != components[ic].vertices[1] &&
          cut0->v2 != components[ic].vertices[1]) {
        n1 = markFrom(components[ic].vertices[1], graph, mark, stack);
      }
      else {
        n1 = markFrom(components[ic].vertices[2], graph, mark, stack);
      }
      if (n1 < s - 2) {
#ifdef VERBOSE
	printf("split2 (with an existing cut) %d -> %d, %d\n", s, n1 + 2, s - n1);
#endif
        components[ic].size = n1 + 2;
        int* vertices = malloc(sizeof(int) * (s - n1));
        int j = 0;
        int k = 0;
        for (int i = 0; i < s; i++) {
          int v = components[ic].vertices[i];
          if (v == cut0->v1 || v == cut0->v2) {
            components[ic].vertices[j++] = v;
            vertices[k++] = v;
          }
          else if (mark[v]) {
            components[ic].vertices[j++] = v;
          }
          else {
            vertices[k++] = v;
          }
        }
        if (nCuts == n) {
          fprintf(stderr, "too many cuts\n");
          exit(1);
        }
        if (nCompo == n) {
          fprintf(stderr, "too many components\n");
          exit(1);
        }
        components[nCompo].size = s - n1;
        components[nCompo].vertices = vertices;
        components[nCompo].nCuts = 0;
        components[nCompo].cuts = malloc(sizeof(CUT*) * (s - n1) * 3);

        j = 0;
        for (int i = 0; i < components[ic].nCuts; i++) {
          CUT* cut = components[ic].cuts[i];
          /* a 1 vertex cut may belong to both components, but
           * we may choose arbitrary one: the bag connections will be fine
           */
          if (indexOf(cut->v1, components[ic].vertices, components[ic].size)
              >= 0 &&
              (cut->v2 == -1 ||
                  indexOf(cut->v2, components[ic].vertices, components[ic].size)
                  >= 0)) {
            components[ic].cuts[j++] = cut;
          }
          else {
            addCut(&components[nCompo], cut);
	    if (cut->ic1 == ic) cut->ic1 = nCompo;
	    else if (cut->ic2 == ic) cut->ic2 = nCompo;
	    else {
	      fprintf(stderr, "cut inconsistency\n");
	      exit(1);
	    }
          }
        }
        components[ic].nCuts = j;

        addCut(&components[ic], &cuts[nCuts]);
        addCut(&components[nCompo], &cuts[nCuts]);

        cuts[nCuts].v1 = cut0->v1;
        cuts[nCuts].v2 = cut0->v2;
        cuts[nCuts].ic1 = ic;
        cuts[nCuts].ic2 = nCompo;
        nCuts++;
        nCompo++;
        continue;
      }
    }

    int stay = 0;
    for (int vc1 = 0; vc1 < s; vc1++) {
      for (int vc2 = vc1 + 1; vc2 < s; vc2++) {
        for (int i = 0; i < s; i++) {
          int v = components[ic].vertices[i];
          mark[v] = 0;
	  if (i == vc1 || i == vc2) {
	    mark[v] = -1;
	  }
        }

        int n1;
        if (vc1 != 0 && vc2 != 0) {
          n1 = markFrom(components[ic].vertices[0], graph, mark, stack);
        }
        else if (vc1 != 1 && vc2 != 1) {
          n1 = markFrom(components[ic].vertices[1], graph, mark, stack);
        }
        else {
          n1 = markFrom(components[ic].vertices[2], graph, mark, stack);
        }
        if (n1 < s - 2) {
#ifdef VERBOSE
	  printf("split2 %d -> %d, %d\n", s, n1 + 2, s - n1);
#endif
	  int theCut1 = components[ic].vertices[vc1];
	  int theCut2 = components[ic].vertices[vc2];

	  addGraphEdge(graph, theCut1, theCut2);

          components[ic].size = n1 + 2;

          int* vertices = vertices = malloc(sizeof(int) * (s - n1));
          int j = 0;
          int k = 0;
          for (int i = 0; i < s; i++) {
            int v = components[ic].vertices[i];
            if (i == vc1 || i == vc2) {
              components[ic].vertices[j++] = v;
              vertices[k++] = v;
            }
            else if (mark[v]) {
              components[ic].vertices[j++] = v;
            }
            else {
              vertices[k++] = v;
            }
          }
          if (nCuts == n) {
            fprintf(stderr, "too many cuts\n");
            exit(1);
          }
          if (nCompo == n) {
            fprintf(stderr, "too many components\n");
            exit(1);
          }
          components[nCompo].size = s - n1;
          components[nCompo].vertices = vertices;
          components[nCompo].nCuts = 0;
          components[nCompo].cuts = malloc(sizeof(CUT*) * (s - n1) * 3);

          j = 0;
          for (int i = 0; i < components[ic].nCuts; i++) {
            CUT* cut = components[ic].cuts[i];
            if (indexOf(cut->v1, components[ic].vertices, components[ic].size)
                >= 0 &&
                (cut->v2 == -1 ||
                    indexOf(cut->v2, components[ic].vertices, components[ic].size)
                    >= 0)) {
              components[ic].cuts[j++] = cut;
            }
            else {
              addCut(&components[nCompo], cut);
	      if (cut->ic1 == ic) cut->ic1 = nCompo;
	      else if (cut->ic2 == ic) cut->ic2 = nCompo;
	      else {
		fprintf(stderr, "cut inconsistency\n");
		exit(1);
	      }
            }
          }
          components[ic].nCuts = j;

          addCut(&components[ic], &cuts[nCuts]);
          addCut(&components[nCompo], &cuts[nCuts]);

          cuts[nCuts].v1 = theCut1;
          cuts[nCuts].v2 = theCut2;
          cuts[nCuts].ic1 = ic;
          cuts[nCuts].ic2 = nCompo;

          nCuts++;
          nCompo++;
	  stay = 1;
	  break;
        }
      }
      if (stay) {
	break;
      }
    }
    if (!stay) ic++;
  }

  /*
  for (ic = 0; ic < nCompo; ic++) {
    checkCuts(components[ic], graph);
  }

  for (int i = 0; i < nCuts; i++) {
    checkCutOwner(&cuts[i], components[cuts[i].ic1]);
    checkCutOwner(&cuts[i], components[cuts[i].ic2]);
  }
  */

#ifdef VERBOSE
  printf("number of components = %d, n = %d\n", ic, n);
#endif


  TD* td = malloc(sizeof(TD));
  td->bags = malloc(sizeof(BAG) * n);
  td->edges = malloc(sizeof(TDEDGE) * n);
  td->width = 1;

  int nb[nCompo + 1];
  int ne[nCompo + 1];
  nb[0] = 0;
  ne[0] = 0;

  for (ic = 0; ic < nCompo; ic++) {
    int s = components[ic].size;
#ifdef VERBOSE
    printf("decomposing %dth component size = %d\n", ic, s);
#endif

    GRAPH* g = malloc(sizeof(GRAPH));

    g -> n = s;
    g -> vertices = malloc(sizeof(VERTEX) * s); 

    for (int i = 0; i < s; i++) {
      int v = components[ic].vertices[i];
      int deg = 0;
      for (int j = 0; j < graph->vertices[v].degree; j++) {
        int w = graph->vertices[v].neighbors[j];
        if (indexOf(w, components[ic].vertices, components[ic].size) >= 0) {
          deg++;
        }
      }

      g -> vertices[i].degree = deg;
      g -> vertices[i].neighbors = malloc(sizeof(int) * deg);
      int k = 0;
      for (int j = 0; j < graph->vertices[v].degree; j++) {
        int w = graph->vertices[v].neighbors[j];
        int u = indexOf(w, components[ic].vertices, components[ic].size);
        if (u >= 0) {
          g -> vertices[i].neighbors[k++] = u;
        }
      }
    }

    TD* td1 = decomposeBody(g);

    if (td1->width > td->width) {
      td->width = td1->width;
    }
    for (int b = 0; b < td1->nBag; b++) {
      td->bags[nb[ic] + b].nv = td1->bags[b].nv;
      td->bags[nb[ic] + b].vertices = 
          invertBag(td1->bags[b], components[ic].vertices);
    }
    for (int i = 0; i < td1->nEdge; i++) {
      td->edges[ne[ic] + i].b1 = td1->edges[i].b1 + nb[ic];
      td->edges[ne[ic] + i].b2 = td1->edges[i].b2 + nb[ic];
    }
    nb[ic + 1] = nb[ic] + td1->nBag;
    ne[ic + 1] = ne[ic] + td1->nEdge;

#ifdef VERBOSE
    printf("decomposed %dth component size = %d\n", ic, s);
#endif
    /*
    freeTD(td1);
    freeGraph(g);
    */
  }

  td->nBag = nb[nCompo];

  int ne1 = ne[nCompo];

  for (int i = 0; i < nCuts; i++) {
    int i1 = cuts[i].ic1;
    int i2 = cuts[i].ic2;
    if (cuts[i].v2 == -1) {
      int b1 = findBagBetween(td, cuts[i].v1, nb[i1], nb[i1 + 1]);
      int b2 = findBagBetween(td, cuts[i].v1, nb[i2], nb[i2 + 1]);
      if (b1 == -1 || b2 == -1) {
        fprintf(stderr, "bag cannot be found for a cut vertex\n");
        exit(1);
      }
      td->edges[ne1].b1 = b1;
      td->edges[ne1].b2 = b2;
      ne1++;
    }
    else {
      int b1 = findBag2Between(td, cuts[i].v1, cuts[i].v2,
          nb[i1], nb[i1 + 1]);
      int b2 = findBag2Between(td, cuts[i].v1, cuts[i].v2,
          nb[i2], nb[i2 + 1]);
      if (b1 == -1 || b2 == -1) {
	/*
	printf("i1 = %d, i2 = %d\n", i1, i2);
	printf("v1 = %d, v2 = %d\n", cuts[i].v1, cuts[i].v2);
	printf("b1 = %d, b2 = %d\n", b1, b2);
	checkCuts(components[i1], graph);
	checkCuts(components[i2], graph);
	*/
        fprintf(stderr, "bag cannot be found for a 2-vetex cut\n");
        exit(1);
      }
      td->edges[ne1].b1 = b1;
      td->edges[ne1].b2 = b2;
      ne1++;
#ifdef VERBOSE
      printf("edge between the %dth and the %dth components added\n", i1, i2);
#endif
    }
  }
  for (int i = 0; i < nCompo; i++) {
    free(components[i].vertices);
    free(components[i].cuts);
  }

  td->nEdge = ne1;
  return td;
}

TD* decomposeBody(GRAPH* graph) {

  if (graph-> n <= 3) {
    return oneBagTree(graph);
  }

  struct timespec current;
  double time_used;
  if (graph->n <= 64) {
#ifdef VERBOSE
    {
      clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &current);
      time_used = ((double) (current.tv_sec - start.tv_sec)) 
	    + (double) (current.tv_nsec - start.tv_nsec) * 0.000000001;
      printf("calling L1 n = %d, time = %lf\n", graph->n, time_used);
    }
#endif
    TD* td = L1decomposeGraph(graph); 
#ifdef VERBOSE
    printf("returned L1 n = %d, width = %d, nBag = %d\n", graph->n,
        td->width, td->nBag);
    if (graph->n > 30) {
      clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &current);
      time_used = ((double) (current.tv_sec - start.tv_sec)) 
	    + (double) (current.tv_nsec - start.tv_nsec) * 0.000000001;
      printf("returned L1 n = %d, time = %lf\n", graph->n, time_used);
    }
#endif
    validate(td, graph);
    return td;
    }
  else
    if (graph->n <= 128) {
#ifdef VERBOSE
      printf("calling L2 n = %d\n", graph->n);
#endif
      TD* td = L2decomposeGraph(graph);

#ifdef VERBOSE
      printf("returned L2 n = %d\n", graph->n);
#endif
      validate(td, graph);
      return td;
    }
    else 
      if (graph->n <= 256) {
#ifdef VERBOSE
        printf("calling L4 n = %d\n", graph->n);
#endif

        TD* td = L4decomposeGraph(graph);

#ifdef VERBOSE
        printf("returned L4 n = %d\n", graph->n);
#endif
        validate(td, graph);
        return td;
      }
      else 
        if (graph->n <= 1024) {
#ifdef VERBOSE
          printf("calling L16 n = %d\n", graph->n);
#endif

          TD* td = L16decomposeGraph(graph);

#ifdef VERBOSE
          printf("returned L16 n = %d\n", graph->n);
#endif
          validate(td, graph);
          return td;
        }
        else
          if (graph->n <= 4096) {
#ifdef VERBOSE
            printf("calling L64 n = %d\n", graph->n);
#endif

            TD* td = L64decomposeGraph(graph);

#ifdef VERBOSE
            printf("returned L64 n = %d, width = %d, nBag = %d\n", graph->n,
                td->width, td->nBag);
#endif
            return td;
          }
          else {
            return NULL;
          }
}

void printDecomposition(TD* td, int n) {
  printf("s td %d %d %d\n", td->nBag, td->width + 1, n);
  for (int b = 0; b < td->nBag; b++) {
    printf("b %d", b + 1);
    for (int i = 0; i < td->bags[b].nv; i++) {
      int v = td->bags[b].vertices[i];
      printf(" ");
      printf("%d", v+1);
    }
    printf("\n");
  }
  for (int j = 0; j < td->nEdge; j++) {
    printf("%d %d\n", td->edges[j].b1 + 1, td->edges[j].b2 + 1);
  } 
}

int main(void) {

  struct timespec end;

  GRAPH* graph = readGraph();

  clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &start);


  TD* td = decompose(graph);

  if (!validate(td, graph)) {
    fprintf(stderr, "validation failed\n"); 
    exit(1);
  }

  clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &end);
  double time_used = ((double) (end.tv_sec - start.tv_sec)) 
        + (double) (end.tv_nsec - start.tv_nsec) * 0.000000001;
  printf("c width = %d, time = %lf\n", td->width, time_used);

#ifdef PRINT
  printDecomposition(td, graph->n);
#endif

  freeTD(td);
  freeGraph(graph);
}
