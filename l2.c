#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include <time.h>
#include "graph.h"
#include "td.h"

/*#define TRACE*/
/*#define DEBUG*/
/*#define VERBOSE*/

#define L 128
#define K 2

#define NB_MAX (1l << 20)
#define HASH_FACTOR 4
/*#define TRIE_FACTOR 20*/
#define TRIE_FACTOR 50
#define WIDTH_MAX 50

typedef struct {
  unsigned long long a[K];
} BSET;

typedef struct {
  BSET component;
  BSET neighbors;
  BSET delta;
} BLOCK;    

typedef struct trieNode {
  BLOCK *block;
  int v;
  struct trieNode *parent;
  struct trieNode *left;
  struct trieNode *right;
} NODE;    

typedef struct {
  BSET key;
  long bi;
} ENTRY;

int n;
BSET *neighborSets;
ENTRY *hashTable;
BSET all;
BSET empty;

unsigned long trieUsed;
NODE *trieRoots[L];
NODE *trieArea;

long nb0;
long nb;
long nbMax;
long trieMax;
long nHash;
long nbHidden;
BLOCK *blocks;

int targetWidth;
int solution;

char dumpPrefix[L];

struct timespec start;

void L2extendBy(NODE *node, int v, BSET c, BSET neighb, BSET from);
void L2extendByIterative(NODE *node, int v, BSET c, BSET neighb, BSET from);
void L2printSet(BSET s);
void L2dumpTrie(NODE *node, int x);

static inline BSET L2emptySet() {
  BSET s;
  for (int i = 0; i < K; i++) {
    s.a[i] = 0;
  }
  return s;
}

static inline void L2add(BSET *s, int i) {
  int w = i / 64;
  int j = i % 64;
  s->a[w] |= 1llu << j;
}

static inline BSET L2fullSet(int n) {
  BSET s = L2emptySet();
  for (int v = 0; v < n; v++) {
    L2add(&s, v);
  }
  return s;
}

static inline int L2equals(BSET s, BSET t) {
  for (int i = 0; i < K; i++) {
    if (s.a[i] != t.a[i]) {
      return 0;
    }
  }
  return 1;
}

static inline void L2unionWith(BSET *s, BSET t) {
  for (int i = 0; i < K; i++) {
    s->a[i] |= t.a[i];
  }
}

static inline void L2intersectWith(BSET *s, BSET t) {
  for (int i = 0; i < K; i++) {
    s->a[i] &= t.a[i];
  }
}

static inline void L2subtract(BSET *s, BSET t) {
  for (int i = 0; i < K; i++) {
    s->a[i] &= ~t.a[i];
  }
}

static inline int L2isSubset(BSET s, BSET t) {
  for (int i = 0; i < K; i++) {
    if ((s.a[i] & ~t.a[i]) != 0) {
      return 0;
    }
  }
  return 1;
}

static inline BSET L2union_(BSET s, BSET t) {
  for (int i = 0; i < K; i++) {
    s.a[i] |= t.a[i];
  }
  return s;
}

static inline BSET L2intersection(BSET s, BSET t) {
  for (int i = 0; i < K; i++) {
    s.a[i] &= t.a[i];
  }
  return s;
}

static inline int L2intersects(BSET s, BSET t) {
  for (int i = 0; i < K; i++) {
    if ((s.a[i] & t.a[i]) != 0) {
      return 1;
    }
  }
  return 0;
}

static inline BSET L2diff(BSET s, BSET t) {
  for (int i = 0; i < K; i++) {
    s.a[i] &= ~t.a[i];
  }
  return s;
}

static inline int L2contains(BSET s, int i) {
  int w = i / 64;
  int j = i % 64;
  return (s.a[w] & (1llu << j)) != 0;
}

static inline int L2firstSetBit(BSET s) {
  for (int k = 0; k < K; k++) {
    if (s.a[k] != 0) {
      long long mask = 1;
      for (int i = 0; i < 64; i++) {
	if ((s.a[k] & mask) != 0) {
	  return k * 64 + i;
	}
	mask << 1;
      }
    }
  }
  return -1;
}

static inline void L2remove_(BSET *s, int i) {
  int w = i / 64;
  int j = i % 64;
  s->a[w] &= ~(1llu << j);
}

static inline int L2bitCount(BSET s) {
  int k = 0;
  int w = 0;
  int j = 0;
  unsigned long long x = s.a[0];
  for (int i = 0; i < n; i++) {
    k += x & 1;
    j++;
    if (j == 64) {
      j = 0;
      x = s.a[++w];
    }
    else {
      x = x >> 1;
    }
  }
  return k;
}

static inline unsigned long L2hash(BSET s) {
  unsigned long h = 0;
  for (int i = 0; i < K; i++) {
    h = (h + s.a[i]) % nHash;
  }
  return h;
}

void L2allocate() {
  nbMax = NB_MAX;
  long* trial; 
  while (1) {
    trieMax = nbMax * TRIE_FACTOR;
    nHash = nbMax * HASH_FACTOR - 1;
    long total = trieMax  * sizeof(NODE) + 
      nHash * sizeof(ENTRY) + 
      nbMax * sizeof(BLOCK) + 
      n * sizeof(BAG) + 
      n * sizeof(TDEDGE) + 
      10 * n * sizeof(int) + /* for bag entries */
      30 * n * sizeof(NODE *); /* for stacks for extendByIterative */
    trial = malloc(total);
    if (trial != NULL) break;
    nbMax /= 2;
  }
  free(trial);
  blocks = (BLOCK *) malloc(nbMax * sizeof(BLOCK));
  trieArea = (NODE *) malloc(trieMax * sizeof(NODE));
  hashTable = (ENTRY *) malloc(nHash * sizeof(ENTRY));

#ifdef VERBOSE
  printf("allocated, nbMax = %ld\n", nbMax);
#endif
}

void L2deallocate() {
  free(hashTable);
  free(trieArea);
  free(blocks);
#ifdef VERBOSE
  printf("deallocated\n");
#endif
}

NODE* L2newNode(int v, BLOCK* block, NODE* left, NODE* right) {
  if (trieUsed == trieMax) {
    fprintf(stderr, "Trie area exhausted\n");
    exit(1);
  }
  trieArea[trieUsed].v = v;
  trieArea[trieUsed].left = left;
  trieArea[trieUsed].right = right;
  trieArea[trieUsed].block = block;
  trieUsed++;
  return &trieArea[trieUsed - 1];
}

void L2clear() {
  nb0 = 0;
  nb = 0;
  nbHidden = 0;
  trieUsed = 0;
  for (int i = 0; i < n; i++) {
    trieRoots[i] = L2newNode(-1, NULL, NULL, L2newNode(n, NULL, NULL, NULL));
    trieRoots[i]->right->parent = trieRoots[i];
  }
  memset(hashTable, 0, nHash * sizeof(ENTRY));
}

long L2getHash(BSET component) {
  unsigned long h = L2hash(component);
  while (!L2equals(hashTable[h].key, empty)) {
    if (L2equals(hashTable[h].key, component)) {
      return hashTable[h].bi;
    }
    h = (h + 1) % nHash;
  }
  return -1;
}

void L2putHash(BSET component, int bi) {
  unsigned long h = L2hash(component);
  while (!L2equals(hashTable[h].key, empty)) {
    if (L2equals(hashTable[h].key, component)) {
      hashTable[h].bi = bi;
      return;
    }
    h = (h + 1) % nHash;
  }
  hashTable[h].key = component;
  hashTable[h].bi = bi;
}

BSET L2closedNeighbor(BSET c) {
  BSET cnb = c;
  for (int v = 0; v < n; v++) {
    if (L2contains(c, v)) {
      L2unionWith(&cnb, neighborSets[v]);
    }
  }
  return cnb;
}

BSET L2saturate(BSET c) {
  BSET cnb = L2closedNeighbor(c);
  BSET neighb = L2diff(cnb, c);
  for (int v = 0; v < n; v++) {
    if (L2contains(neighb, v)) {
      if (L2isSubset(neighborSets[v], cnb)) {
        L2add(&c, v);
      }        
    }
  }
  return c;
}

void L2registerBlock0(BSET component, BSET neighbors, BSET delta) {  
  if (L2getHash(component) >= 0) {
    return;
  }

  if (nb + nbHidden == nbMax) {
    fprintf(stderr, "block area exausted\n");
    exit(1);
  }

  if (L2bitCount(component) >= n - targetWidth - 1) {
    solution = nb;
#ifdef TRACE
    printf("solution: ");
    L2printSet(component);
    printf(",");
    L2printSet(neighbors);
    printf("\n");
#endif
  }
  blocks[nb].component = component;
  blocks[nb].neighbors = neighbors;
  blocks[nb].delta = delta;
  L2putHash(component, nb);

  nb++;

  #ifdef TRACE
  printf("registered ");
  L2printSet(component);
  printf(":");
  L2printSet(neighb);
  printf(":");
  L2printSet(delta);
  printf("\n");
  #endif
}

void L2addHiddenBlock(BSET component, BSET neighbors, BSET delta) {
  long b = L2getHash(component);
  if (b >= 0) {
    return;
  }
  if (nb + nbHidden == nbMax) {
    fprintf(stderr, "block area exausted\n");
    exit(1);
  }

  nbHidden++;
  blocks[nbMax - nbHidden].component = component;
  blocks[nbMax - nbHidden].neighbors = neighbors;
  blocks[nbMax - nbHidden].delta = delta;
  L2putHash(component, nbMax - nbHidden);
}

void L2registerForVertex(int v, BLOCK *block) {
#ifdef DEBUG
  printf("registerForVertex %d:", v);
  L2printSet(block->component);
  printf("\n");
#endif

  NODE* p = trieRoots[v]->right;
  for (int w = 0; w < n; w++) {
    if (L2contains(block->component, w)) {
      while (p->v < w) {
        p = p->left;
      }
      if (p->v == w) {
        p = p->right;
      }
      else {
        NODE* tn = L2newNode(w, NULL, p,
            L2newNode(n, NULL, NULL, NULL));
        tn->parent = p->parent;
        if (p == p->parent->left) {
          p->parent->left = tn;
        }
        else {
          p->parent->right = tn;
        }
        p->parent = tn;
        tn->right->parent = tn;

        p = tn->right;
      }
    }
  }
#ifdef DEBUG
  printf("registerForVertex, registered %d:\n", v);
#endif
  p->block = block;
}

void L2registerBlock(BSET component, BSET delta) {
#ifdef TRACE
  printf("registering ");
  L2printSet(component);
  printf(":");
  L2printSet(delta);
  printf("\n");
#endif

  BSET neighb = L2diff(L2closedNeighbor(component), component);

#ifdef DEBUG
  printf("neighbor set:");
  L2printSet(neighb);
  printf("\n");
#endif

  if (L2bitCount(neighb) + L2bitCount(delta) > targetWidth + 1) {
#ifdef DEBUG
    printf("too large neighborhood ");
    L2printSet(component);
    printf(":");
    L2printSet(neighb);
    printf("\n");
#endif
    return;
  }

  L2registerBlock0(component, neighb, delta);
}

void L2process(BLOCK *b) {
  for (int v = 0; v < n; v++) {
    if (L2contains(b->neighbors, v)) {
      L2registerForVertex(v, b);

      /*
      printf("L2dumping trie for %d after adding ", v);
      L2printSet(b->component);
      printf("\n");
      L2dumpTrie(trieRoots[v]->right, 0);
      */

      BSET c = b->component;
      L2add(&c, v);
      c = L2saturate(c);
      L2registerBlock(c, L2diff(c, b->component));

/*
      L2extendBy(trieRoots[v]->right, v, b->component,
          b->neighbors, empty);
*/
      L2extendByIterative(trieRoots[v], v, b->component,
          b->neighbors, empty);
      if (solution >= 0) {
        return;
      }
    }
  }
}

int L2anAbsorbable(BSET vertices, BSET neighbors) {
  for (int v = 0; v < n; v++) {
    if (L2contains(neighbors, v) &&
        L2isSubset(neighborSets[v], L2union_(vertices, neighbors))) {
      return v;
    }
  }
  return -1;
}

void L2extendByIterative(NODE* node, int v, BSET c, BSET neighb, BSET from) {
  /* an entry in the stack means that the righ child of the node is
     still to be processed 
  */
  NODE* stack[n];
  stack[0] = node;
  int top = 0;
  while (top >= 0) {
    node = stack[top--];
    /* bug fix Aig 09, 2016 */
    if (!L2contains(from, node->v)) {
      from = L2emptySet();
    }
    node = node->right;
#ifdef TRACE
    printf("%d:%d,", v, node->v);
    L2printSet(c);
    printf(",");
    L2printSet(neighb);
    printf(",");
    L2printSet(from);
    printf(", %ld", node->block);
    printf("\n");

#endif
    while (node != NULL) {
      if (node -> block != NULL) {
#ifdef TRACE
        printf("block = ");
        L2printSet(node->block->component);
        printf(",");
        L2printSet(node->block->neighbors);
        printf("\n");
#endif
	if (L2equals(node->block->component, from)) {
	  node = NULL;
	  continue;
	} 
	if (L2intersects(node->block->component, L2union_(c, neighb))) {
	  fprintf(stderr, "trie search inconsistent for %d\n", v);
	  /*
	    L2printSet(c); printf(",");
	    L2printSet(neighb); printf("\n");
	  */
	  exit(1);
	}

	BSET neighb1 = L2union_(neighb, node->block->neighbors);

	if (L2bitCount(neighb1) <= targetWidth + 1) {
	  BSET c1 = L2union_(c, node->block->component);
	  int absorbable = L2anAbsorbable(c1, neighb1);

	  if (absorbable < 0 || absorbable == v) {
	    BSET c2 = c1;
	    L2add(&c2, v);
	    BSET c3 = L2saturate(c2);
	    L2registerBlock(c3, L2diff(c3, c1));
	  }
	  if (solution >= 0) {
	    node = NULL;
	    continue;
	  }

	  if (absorbable < 0) {
	    L2extendByIterative(trieRoots[v], v, c1, neighb1,
				 node->block->component);
	  }
	}
      }
      if (node->right != NULL && 
	    !L2contains(L2union_(c, neighb), node->v)) {
	  stack[++top] = node;
      }

      if (node->left != NULL && !L2contains(from, node->v)) {
	node = node->left;
      }
      else {
        node = NULL;
      }
    }
  }
}

void L2extendBy(NODE* node, int v, BSET c, BSET neighb, BSET from) {
#ifdef TRACE
  printf("%d:%d,", v, node->v);
  L2printSet(c);
  printf(",");
  L2printSet(neighb);
  printf(",");
  L2printSet(from);
  printf(", %ld", node->block);
  printf("\n");

#endif
  if (node -> block != NULL) {
#ifdef TRACE
    printf("block = ");
    L2printSet(node->block->component);
    printf(",");
    L2printSet(node->block->neighbors);
    printf("\n");
#endif
    if (L2equals(node->block->component, from)) {
      return;
    } 
    if (L2intersects(node->block->component, L2union_(c, neighb))) {
      fprintf(stderr, "trie search inconsistent for %d\n", v);
      /*
	L2printSet(c); printf(",");
	L2printSet(neighb); printf("\n");
      */
      exit(1);
    }

    BSET neighb1 = L2union_(neighb, node->block->neighbors);

    if (L2bitCount(neighb1) <= targetWidth + 1) {
      BSET c1 = L2union_(c, node->block->component);
      int absorbable = L2anAbsorbable(c1, neighb1);

      if (absorbable < 0 || absorbable == v) {
        BSET c2 = c1;
        L2add(&c2, v);
        BSET c3 = L2saturate(c2);
        L2registerBlock(c3, L2diff(c3, c1));
      }
      if (solution >= 0) {
        return;
      }

      if (absorbable < 0) {
        L2extendBy(trieRoots[v]->right, v, c1, neighb1,
		    node->block->component);
      }
    }
  }
  if (node->left != NULL && !L2contains(from, node->v)) {
    L2extendBy(node->left, v, c, neighb, from);
    if (solution >= 0) {
      return;
    }
  }
  if (node->right != NULL && 
      !L2contains(L2union_(c, neighb), node->v)) {
    L2extendBy(node->right, v, c, neighb, from);
  }

}

void L2decompose() {
#ifdef VERBOSE
  printf("decomose enter\n");
#endif

  targetWidth = 1;
  solution = -1;
  while (solution < 0) {
#ifdef VERBOSE
    printf("target width = %d\n", targetWidth);
#endif
    L2clear();
    for (int v = 0; v < n; v++) {
      if (L2bitCount(neighborSets[v]) <= targetWidth) {
        BSET c = L2emptySet();
        L2add(&c, v);
        BSET c1 = L2saturate(c);
	/*
        L2printSet(c1); printf(" ... c1, %d\n", v);
	*/
        L2registerBlock(c1, c1);
      }
    }
    while (nb > nb0 && solution < 0) {
#ifdef VERBOSE
      struct timespec current;
      clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &current);
      double time_used = ((double) (current.tv_sec - start.tv_sec)) 
	    + (double) (current.tv_nsec - start.tv_nsec) * 0.000000001;
      printf("  nb0 = %ld, nb = %ld, time = %lf\n", nb0, nb, time_used);
#endif
      int nb1 = nb;
      for (int i = nb0; i < nb1; i++) {
        L2process(&blocks[i]);
        if (solution >= 0) {
          break;
        }
      }
      nb0 = nb1;
    }
    if (solution < 0) {
      targetWidth++;
      fprintf(stderr, "width = %d\n", targetWidth);
    }
  }
#ifdef VERBOSE
  printf("width = %d\n", targetWidth);
#endif
}

void L2printSet(BSET s) {
  for (int k = n - 1; k >= 0; k--) {
    if (L2contains(s, k)) {
      putchar('1');
    }
    else {
      putchar('0');
    }
  }
}

void L2dumpTrie(NODE* node, int x) {
  if (node == NULL) {
    return;
  }
  if (node -> block != NULL) {
    if (x > 0) {
      printf("%s:", dumpPrefix);
    }
    L2printSet(node->block->component);
    printf(",");
    L2printSet(node->block->neighbors);
    printf("\n");
    return;
  }
  if (node->v == x) {
    dumpPrefix[x] = 'l';
    dumpPrefix[x + 1] = 0;
    L2dumpTrie(node->left, x + 1);
    dumpPrefix[x] = 'r';
    dumpPrefix[x + 1] = 0;
    L2dumpTrie(node->right, x + 1);
  }
  else {
    dumpPrefix[x] = 'd';
    dumpPrefix[x + 1] = 0;
    L2dumpTrie(node, x + 1);
  }
}

BAG L2makeBag(BSET s) {
  BAG bag;
  bag.nv = L2bitCount(s);
  bag.vertices = (int*) malloc(sizeof(int) * bag.nv);
  int k = 0;
  for (int v = 0; v < n; v++) {
    if (L2contains(s, v)) {
      bag.vertices[k++] = v;
    }
  }
  return bag;
}

int L2addBag(BSET s, TD* td) {
  int k = td->nBag;
  if (k == n) {
    fprintf(stderr, "too many bags\n");
    exit(1);
  }
  td->bags[k] = L2makeBag(s);
  (td->nBag)++;
  return k;
}

void L2addTDEdge(int k, int j, TD* td) {
  int i = td->nEdge;
  if (i == n) {
    fprintf(stderr, "too many decomposition edges\n");
    exit(1);
  }
  td->edges[i].b1 = k;
  td->edges[i].b2 = j;
  (td->nEdge)++;
}

int L2getComponents(BSET vertices, BSET components[]) {
  int p = 0;
  BSET vs = vertices;
  for (int v = 0; v < n; v++) {
    if (L2contains(vs, v)) {
      BSET nb = neighborSets[v];
      L2add(&nb, v);
      BSET c = L2intersection(nb, vertices);
      while (1) {
        BSET c1 = c;
        for (int w = 0; w < n; w++) {
          if (L2contains(c1, w)) {
            L2unionWith(&c1, neighborSets[w]);
            L2intersectWith(&c1, vertices);
          }
        }
        if (L2equals(c1, c)) {
          break;
        }
        c = c1;
      }
      components[p++] = c;
      L2subtract(&vs, c);
    }
  }
  return p;
}

BLOCK* L2getBlock(BSET c) {
  long bi = L2getHash(c);
  if (bi < 0) {
    fprintf(stderr, "block not in hash unexpectedly");
    exit(1);
  }
  return &blocks[bi];
}


int L2toTD(BLOCK* block, TD* td) {
  BLOCK* bStack[n];
  int aStack[n];
  BSET components[n];

  bStack[0] = block;
  aStack[0] = -1;
  int top = 0;

  int r;

  while (top >= 0) {
    BLOCK* b = bStack[top];
    int k = aStack[top];
    top--;
    if (L2bitCount(b->component) + L2bitCount(b->neighbors)
      <= targetWidth + 1) {
      int j = L2addBag(L2union_(b->component, b->neighbors), td);
      if (k >= 0) {
	L2addTDEdge(k, j, td);
      }
      else r = j;
      continue;
    }
    BSET s = L2union_(b->neighbors, b->delta);
    /*  L2printSet(b->neighbors);
	printf(",");
	L2printSet(b->delta);
	printf("\n");
    */

    int j = L2addBag(s, td);
    if (k >= 0) {
      	L2addTDEdge(k, j, td);
    }
    else {
      r = j;
    }
    BSET base = L2diff(b->component, b->delta);
    int m = L2getComponents(base, components);
    for (int i = 0; i < m; i++) {
      top++;
      bStack[top] = L2getBlock(components[i]);
      aStack[top] = j;
    }
  }
  return r;
}

TD* L2decomposeGraph(GRAPH* graph) {
#ifdef VERBOSE
  clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &start);
  printf("L2decomposeGrah enter n = %d\n", graph-> n);
#endif

  n = graph->n;
  all = L2fullSet(n);
  empty = L2emptySet();

  neighborSets = (BSET*) malloc(sizeof(BSET) * n);
  for (int v = 0; v < n; v++) {
    neighborSets[v] = L2emptySet();
  }
  for (int v = 0; v < n; v++) {
    for (int i = 0; i < graph->vertices[v].degree; i++) {
      int w = graph->vertices[v].neighbors[i];
      L2add(&neighborSets[v], w);
      L2add(&neighborSets[w], v);
    }
  }

  L2allocate();
  L2decompose();

  TD* td = (TD*) malloc(sizeof(TD));
  td->nBag = 0;
  td->nEdge = 0;
  td->width = targetWidth;
  td->bags = (BAG*) malloc(sizeof(BAG) * n);
  td->edges = (TDEDGE*)malloc(sizeof(TDEDGE) * n);

  BSET s = L2diff(all, blocks[solution].component);
  if (!L2equals(s, empty)) {
    int  k = L2addBag(s, td);
    int j = L2toTD(&blocks[solution], td);
    L2addTDEdge(k, j, td);
  }
  else {
    L2toTD(&blocks[solution], td);
  }
  L2deallocate();
  free(neighborSets);
  return td;
}



