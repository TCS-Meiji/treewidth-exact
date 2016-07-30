#include <stdio.h>
#include <stdlib.h>
#include "graph.h"

int indexOf(int x, int a[], int n) {
  for (int i = 0; i < n; i++) {
    if (a[i] == x) return i;
  }
  return -1;
}

void addGraphEdge(GRAPH* graph, int u, int v) {
  if (indexOf(u, graph->vertices[v].neighbors, graph->vertices[v].degree) >= 0) {
    return;
  }
  int* neighbors = malloc(sizeof(int) * (graph->vertices[v].degree + 1));
  for (int i = 0; i < graph->vertices[v].degree; i++) {
    neighbors[i] = graph->vertices[v].neighbors[i];
  }
  neighbors[graph->vertices[v].degree] = u;

  free(graph->vertices[v].neighbors);
  graph->vertices[v].neighbors = neighbors;
  graph->vertices[v].degree++;

  neighbors = malloc(sizeof(int) * (graph->vertices[u].degree + 1));
  for (int i = 0; i < graph->vertices[u].degree; i++) {
    neighbors[i] = graph->vertices[u].neighbors[i];
  }
  neighbors[graph->vertices[u].degree] = v;
  free(graph->vertices[u].neighbors);
  graph->vertices[u].neighbors = neighbors;
  graph->vertices[u].degree++;
}

int numberOfEdges(GRAPH* graph) {
  int k = 0;
  for (int v = 0; v < graph->n; v++) {
    k += graph->vertices[v].degree;
  }
  return k / 2;
}

int numberOfDeg2Vertices(GRAPH* graph) {
  int k = 0;
  for (int v = 0; v < graph->n; v++) {
    if (graph->vertices[v].degree == 2) {
      k++;
    }
  }
  return k;
}

int theOtherEndOfChain(int w, GRAPH* graph, int parent[]) {
  int current = w;
  while (1) {
    int next = theOtherNeighbor(current, parent[current], graph);
    if (parent[next] == -1) {
      break;
    }
    current = next;
  }
  return current;
}

int theOtherAttachmentOfChain(int v, int w, GRAPH* graph, int parent[]) {
  int current = v;
  int next = w;
  while (parent[next] >= 0) {
    int newNext = theOtherNeighbor(next, current, graph);
    current = next;
    next = newNext;
  }
  return next;
}

GRAPH* convertWithEdge(GRAPH* graph, int n,
    int conv[], int inv[], int cut1, int cut2) {
  GRAPH* g = malloc(sizeof(GRAPH));
  g->n = n;
  g->vertices = malloc(sizeof(VERTEX) * n);
  for (int v = 0; v < n; v++) {
    int degree = 0;
    VERTEX vertex = graph->vertices[inv[v]];
    for (int i = 0; i < vertex.degree; i++) {
      if (conv[vertex.neighbors[i]] >= 0) {
        degree++;
      }
    }
    if (inv[v] == cut1 || inv[v] == cut2) {
      degree++;
    }

    g->vertices[v].degree = degree;
    g->vertices[v].neighbors = malloc(sizeof(int) * degree);

    int k = 0;
    for (int i = 0; i < vertex.degree; i++) {
      int w = conv[vertex.neighbors[i]];
      if (w >= 0) {
        g->vertices[v].neighbors[k++] = w;
      }
    }
    if (inv[v] == cut1) {
      g->vertices[v].neighbors[degree - 1] = conv[cut2];
    }
    else if (inv[v] == cut2) {
      g->vertices[v].neighbors[degree - 1] = conv[cut1];
    }
  }
  return g;
}

int theOtherNeighbor(int v, int aNeighbor, GRAPH* graph) {
  VERTEX vertex = graph->vertices[v];
  if (vertex.degree != 2) {
    fprintf(stderr, "the degree of vertex %d is assumed to be 2, but actually is %d\n",
        v, vertex.degree);
    exit(1);
  }
  if (vertex.neighbors[0] == aNeighbor) {
    return vertex.neighbors[1];
  }
  else if (vertex.neighbors[1] == aNeighbor) {
    return vertex.neighbors[0];
  }
  else {
    fprintf(stderr, "vertex %d is assumed to have neighbor %d but does not\n",
        v, aNeighbor);
    exit(1);
  }
}

GRAPH* convert(GRAPH* graph, int n, int conv[], int inv[]) {
  GRAPH* g = malloc(sizeof(GRAPH));
  g->n = n;
  g->vertices = malloc(sizeof(VERTEX) * n);
  for (int v = 0; v < n; v++) {
    int degree = 0;
    VERTEX vertex = graph->vertices[inv[v]];
    for (int i = 0; i < vertex.degree; i++) {
      if (conv[vertex.neighbors[i]] >= 0) {
        degree++;
      }
    }
    g->vertices[v].degree = degree;

    g->vertices[v].neighbors = malloc(sizeof(int) * degree);

    int k = 0;
    for (int i = 0; i < vertex.degree; i++) {
      /*      printf("%d, %d, %d, %d\n", v, inv[v], i, k);
       */
      int w = conv[vertex.neighbors[i]];
      if (w != -1) {
        if (w < 0 || w >= n) {
          fprintf(stderr, "converted vertex number %d invalid for n = %d\n", 
              w, n);
          exit(1);
        }
        g->vertices[v].neighbors[k++] = w;
      }
    }
  }
  return g;
}

GRAPH* contractChains(GRAPH* graph,
    int n1, int parent[], int conv[]) {
  int n = graph->n;
  GRAPH* graph1 = malloc(sizeof(GRAPH));
  graph1->n = n1;
  graph1->vertices = malloc(sizeof(VERTEX) * n1);

  for (int v = 0; v < n; v++) {
    if (parent[v] >= 0) continue;
    VERTEX vertex = graph->vertices[v];
    int k = conv[v];
    /* printf("k = %d, v = %d, n = %d, n1 = %d\n", k, v, n, n1);
     */
    graph1->vertices[k].degree = vertex.degree;
    graph1->vertices[k].neighbors =
        malloc(sizeof(int) * vertex.degree);

    for (int i = 0; i < vertex.degree; i++) {
      int z = vertex.neighbors[i];
      /*      printf("i = %d, z = %d\n", i, z);
       */
      if (parent[z] >= 0) {
        z = theOtherAttachmentOfChain(v, z, graph, parent);
      }
      graph1->vertices[k].neighbors[i] = conv[z];
    }
  }
  return graph1;
}

void dumpGraph(GRAPH* graph) {
  printf("n = %d\n", graph->n);
  for (int i = 0; i < graph -> n; i++) {
    /*printf("%d: %d, %d\n",i, graph->vertices[i].degree, graph->vertices[i].neighbors);
     */
    for (int j = 0; j < graph->vertices[i].degree; j++) {
      printf("%d, %d\n", i, graph->vertices[i].neighbors[j]);
      fflush(stdout);
    }
  }
}

void markWith(int c, int v, GRAPH* graph, int mark[], int stack[]) {
  stack[0] = v;
  int top = 0;
  while (top >= 0) {
    v = stack[top--];
    if (mark[v] >= 0) {
      continue;
    }
    mark[v] = c;
    for (int j = 0; j < graph->vertices[v].degree; j++) {
      int w = graph->vertices[v].neighbors[j];
      stack[++top] = w;
    }
  }
}

int markComponents(GRAPH* graph, int mark[]) {
  int stack[numberOfEdges(graph) * 2];
  int nc = 0;
  for (int v = 0; v < graph -> n; v++) {
    if (mark[v] == -1) {
      markWith(nc++, v, graph, mark, stack);
    }
  }
  return nc;
}

int markFrom(int v, GRAPH* graph, int mark[], int stack[]) {
  int top = 0;
  stack[0] = v;
  int k = 0;
  while (top >= 0) {
    v = stack[top--];
    if (mark[v]) {
      continue;
    }
    k++;
    mark[v] = 1;
    for (int j = 0; j < graph->vertices[v].degree; j++) {
      int w = graph->vertices[v].neighbors[j];
      stack[++top] = w;
    }
  }
  return k;
}

int markDeg2Chains(GRAPH* graph, int parent[]) {
  int k = 0;
  VERTEX* vertices = graph->vertices;
  for (int v = 0; v < graph->n; v++) {
    if (parent[v] >= 0 || vertices[v].degree > 2) {
      continue;
    }

    int w = vertices[v].neighbors[0];
    int z = vertices[v].neighbors[1];
    int s = -1;

    if (vertices[w].degree > 2) {

      s = w;
    }
    else if (vertices[z].degree > 2) {
      s = z;
    }
    if (s == -1) {
      continue;
    }
    int current = v;
    int next = theOtherNeighbor(current, s, graph);

    while (1) {
      parent[current] = next;
      k++;
      if (vertices[next].degree > 2) {
        break;
      }
      int newNext = theOtherNeighbor(next, current, graph);
      current = next;
      next = newNext;
    }
  }
  return k;
}

