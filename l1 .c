#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include <time.h>
#include "graph.h"
#include "td.h"

/*#define TRACE*/
/*#define DEBUG*/
/*#define VERBOSE*/

#define L 64
#define K 1

#define NB_MAX (1l << 20)
#define HASH_FACTOR 4
/*#define TRIE_FACTOR 20*/
#define TRIE_FACTOR 100
#define WIDTH_MAX 50

typedef unsigned long long int LONG;
typedef struct {
  LONG component;
  LONG neighbors;
  LONG delta;
} BLOCK;    

typedef struct trieNode {
  BLOCK *block;
  int v;
  struct trieNode *parent;
  struct trieNode *left;
  struct trieNode *right;
} NODE;    

typedef struct {
  LONG key;
  long bi;
} ENTRY;

int n;
LONG *neighborSets;
ENTRY *hashTable;
LONG all;

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

char dumpPrefix[65];

struct timespec start;

void L1extendBy(NODE *node, int v, LONG c, LONG neighb, LONG from);
int L1bitCount(LONG s);
void L1printSet(LONG s);
void L1dumpTrie(NODE *node, int x);

void L1allocate() {
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
  printf("L1allocated\n");
#endif
}

void L1deallocate() {
  free(hashTable);
  free(trieArea);
  free(blocks);
#ifdef VERBOSE
  printf("L1deallocated\n");
#endif
}

NODE* L1newNode(int v, BLOCK* block, NODE* left, NODE* right) {
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
  
void L1clear() {
  nb0 = 0;
  nb = 0;
  nbHidden = 0;
  trieUsed = 0;
  for (int i = 0; i < n; i++) {
    trieRoots[i] = L1newNode(-1, NULL, L1newNode(n, NULL, NULL, NULL), NULL);
    trieRoots[i]->left->parent = trieRoots[i];
  }
  memset(hashTable, 0, nHash * sizeof(ENTRY));
}

long L1getHash(LONG component) {
  unsigned long h = (unsigned long) (component % nHash);
  while (hashTable[h].key != 0) {
    if (hashTable[h].key == component) {
      return hashTable[h].bi;
    }
    h = (h + 1) % nHash;
  }
  return -1;
}
  
void L1putHash(LONG component, int bi) {
  unsigned long h = (unsigned long) (component % nHash);
  while (hashTable[h].key != 0) {
    if (hashTable[h].key == component) {
      hashTable[h].bi = bi;
      return;
    }
    h = (h + 1) % nHash;
  }
  hashTable[h].key = component;
  hashTable[h].bi = bi;
}
  
LONG L1closedNeighbor(LONG c) {
  LONG cnb = c;
  for (int v = 0; v < n; v++) {
    if ((c & (1llu << v)) != 0) {
      cnb |= neighborSets[v];
    }
  }
  return cnb;
}
  
LONG L1saturate(LONG c) {
  LONG cnb = L1closedNeighbor(c);
  LONG neighb = cnb & ~c;
  for (int v = 0; v < n; v++) {
    if ((neighb & (1llu << v)) != 0) {
      LONG vnb = neighborSets[v];
      if ((~cnb & vnb) == 0) {
	c |= 1llu << v;
      }        
    }
  }
  return c;
}

void L1addHiddenBlock(LONG component, LONG neighbors, LONG delta) {
  long b = L1getHash(component);
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
  L1putHash(component, nbMax - nbHidden);
}

void L1registerBlock0(LONG component, LONG neighbors, LONG delta) {  
  if (L1getHash(component) >= 0) {
    return;
  }

  if (nb + nbHidden == nbMax) {
    fprintf(stderr, "block area exausted\n");
    exit(1);
  }

  if (L1bitCount(component) >= n - targetWidth - 1) {
    solution = nb;
#ifdef TRACE
    printf("solution: ");
    L1printSet(component);
    printf(",");
    L1printSet(neighbors);
    printf("\n");
#endif
  }
  blocks[nb].component = component;
  blocks[nb].neighbors = neighbors;
  blocks[nb].delta = delta;
  L1putHash(component, nb);

  nb++;

  #ifdef TRACE
  printf("registered ");
  L1printSet(component);
  printf(":");
  L1printSet(neighb);
  printf(":");
  L1printSet(delta);
  printf("\n");
  #endif
}

void L1registerForVertex(int v, BLOCK *block) {
#ifdef DEBUG
  printf("L1registerForVertex %d:", v);
  L1printSet(block->component);
  printf("\n");
#endif

  NODE* p = trieRoots[v]->left;
  for (int w = 0; w < n; w++) {
    if ((block->component & (1llu << w)) != 0) {
      while (p->v < w) {
	p = p->left;
      }
      if (p->v == w) {
	p = p->right;
      }
      else {
	NODE* tn = L1newNode(w, NULL, p,
			     L1newNode(n, NULL, NULL, NULL));
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
  p->block = block;
}

void L1registerBlock(LONG component, LONG delta) {
#ifdef TRACE
  printf("registering ");
  L1printSet(component);
  printf(":");
  L1printSet(delta);
  printf("\n");
#endif
    
  LONG neighb = L1closedNeighbor(component) & ~component;

#ifdef DEBUG
  printf("neighbor set:");
  L1printSet(neighb);
  printf("\n");
#endif

  if (L1bitCount(neighb) + L1bitCount(delta) > targetWidth + 1) {
#ifdef DEBUG
    printf("too large neighborhood ");
      L1printSet(component);
      printf(":");
      L1printSet(neighb);
      printf("\n");
      #endif
    return;
  }
  L1registerBlock0(component, neighb, delta);
}

void L1process(BLOCK *b) {
  for (int v = 0; v < n; v++) {
    if ((b->neighbors & (1llu << v)) != 0) {
      L1registerForVertex(v, b);

      /*
      printf("dumping trie for %d after adding ", v);
      L1printSet(b->component);
      printf("\n");
      L1dumpTrie(trieRoots[v]->left, 0);
      */

      LONG c = b->component | (1llu << v);
      c = L1saturate(c);
      L1registerBlock(c, c & ~b->component);

      L1extendBy(trieRoots[v]->left, v, b->component,
	       b->neighbors, 0);
      if (solution >= 0) {
	return;
      }
    }
  }
}

int L1anAbsorbable(LONG vertices, LONG neighbors) {
  for (int v = 0; v < n; v++) {
    if ((neighbors & (1llu << v)) !=0 &&
        neighborSets[v] & ~(vertices | neighbors) == 0) {
      return v;
    }
  }
  return -1;
}

void L1extendBy(NODE* node, int v, LONG c, LONG neighb, LONG from) {
#ifdef TRACE
  printf("%d:%d,", v, node->v);
  L1printSet(c);
  printf(",");
  L1printSet(neighb);
  printf(",");
  L1printSet(from);
  printf("\n");
#endif
  if (node -> block != NULL) {
#ifdef TRACE
    printf("block = ");
    L1printSet(node->block->component);
    printf(",");
    L1printSet(node->block->neighbors);
    printf("\n");
#endif
    if (node->block->component == from) {
      return;
    } 
    if ((node->block->component & (c | neighb)) != 0) {
      fprintf(stderr, "trie search inconsistent for %d\n", v);
      /*      L1printSet(c); printf(",");
      L1printSet(neighb); printf("\n");
      */
      exit(1);
    }
      
    LONG neighb1 = neighb | node->block->neighbors;
      
    if (L1bitCount(neighb1) <= targetWidth + 1) {
      LONG c1 = c | node->block->component;
      int absorbable = L1anAbsorbable(c1, neighb1);

      if (absorbable < 0 || absorbable == v) {
	LONG c2 = c1 | (1llu << v);
	LONG c3 = L1saturate(c2);
	L1registerBlock(c3, c3 & ~c1);
      }
      if (solution >= 0) {
	return;
      }

      if (absorbable < 0) {
	L1extendBy(trieRoots[v]->left, v, c1, neighb1,
	       node->block->component);
      }
    }
  }
  if (node->left != NULL && (from & (1llu << node->v)) == 0) {
    L1extendBy(node->left, v, c, neighb, from);
    if (solution >= 0) {
      return;
    }
  }
  if (node->right != NULL && 
      ((c | neighb) & (1llu << node->v)) == 0) {
    /* but fix Aug 09, 2016*/
    if ((from & (1llu << node->v)) == 0) {
      L1extendBy(node->right, v, c, neighb, 0);
    }
    else {
      L1extendBy(node->right, v, c, neighb, from);
    }
  }
}

void L1decompose() {
#ifdef VERBOSE
  printf("decomose enter\n");
#endif

  targetWidth = 1;
  solution = -1;
  while (solution < 0) {
#ifdef VERBOSE
    printf("target width = %d\n", targetWidth);
#endif
    L1clear();
    for (int v = 0; v < n; v++) {
      if (L1bitCount(neighborSets[v]) <= targetWidth) {
	LONG c = 1llu << v;
	LONG c1 = L1saturate(c);
	L1registerBlock(c1, c1);
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
	L1process(&blocks[i]);
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

int L1bitCount(LONG s) {
  int k = 0;
  for (int i = 0; i < n; i++) {
    if ((s & (1llu << i)) != 0) {
      k++;
    }
  }
  return k;
}
 
void L1printSet(LONG s) {
  for (int k = n - 1; k >= 0; k--) {
    if ((s & (1llu << k)) != 0) {
      putchar('1');
    }
    else {
      putchar('0');
    }
  }
}

void L1dumpTrie(NODE* node, int x) {
  if (node == NULL) {
    return;
  }
  if (node -> block != NULL) {
    if (x > 0) {
      printf("%s:", dumpPrefix);
    }
    L1printSet(node->block->component);
    printf(",");
    L1printSet(node->block->neighbors);
    printf("\n");
    return;
  }
  if (node->v == x) {
    dumpPrefix[x] = 'l';
    dumpPrefix[x + 1] = 0;
    L1dumpTrie(node->left, x + 1);
    dumpPrefix[x] = 'r';
    dumpPrefix[x + 1] = 0;
    L1dumpTrie(node->right, x + 1);
  }
  else {
    dumpPrefix[x] = 'd';
    dumpPrefix[x + 1] = 0;
    L1dumpTrie(node, x + 1);
  }
}

BAG L1makeBag(LONG s) {
  BAG bag;
  bag.nv = L1bitCount(s);
  bag.vertices = (int*) malloc(sizeof(int) * bag.nv);
  int k = 0;
  for (int v = 0; v < n; v++) {
    if ((s & (1llu << v)) != 0) {
      bag.vertices[k++] = v;
    }
  }
  return bag;
}

int L1addBag(LONG s, TD* td) {
  int k = td->nBag;
  if (k == n) {
    fprintf(stderr, "too many bags\n");
    exit(1);
  }
  td->bags[k] = L1makeBag(s);
  (td->nBag)++;
  return k;
}

void L1addTDEdge(int k, int j, TD* td) {
  int i = td->nEdge;
  if (i == n) {
    fprintf(stderr, "too many decomposition edges\n");
    exit(1);
  }
  td->edges[i].b1 = k;
  td->edges[i].b2 = j;
  (td->nEdge)++;
}

int L1getComponents(LONG vertices, LONG components[]) {
  int p = 0;
  LONG vs = vertices;
  for (int v = 0; v < n; v++) {
    if ((vs & (1llu << v)) != 0) {
      LONG c = (neighborSets[v] | (1llu << v)) & vertices;
      while (1) {
        LONG c1 = c;
        for (int w = 0; w < n; w++) {
          if ((c1 & (1llu << w)) != 0) {
            c1 |= neighborSets[w];
            c1 &= vertices;
	  }
	}
        if (c1 == c) {
          break;
	}
        c = c1;
      }
      components[p++] = c;
      vs = vs & ~c;
    }
  }
  return p;
}

BLOCK L1getBlock(LONG c) {
  long bi = L1getHash(c);
  if (bi < 0) {
    fprintf(stderr, "block not in hash unexpectedly");
    exit(1);
  }
  return blocks[bi];
}


int L1toTD(BLOCK block, TD* td) {
  if (L1bitCount(block.component) + L1bitCount(block.neighbors)
      <= targetWidth + 1) {
    return L1addBag(block.component | block.neighbors, td);
  }

  LONG s = block.neighbors | block.delta;
  /*  L1printSet(block.neighbors);
  printf(",");
  L1printSet(block.delta);
  printf("\n");
  */

  int k = L1addBag(s, td);

  LONG base = block.component &~block.delta;
  LONG components[L1bitCount(base)];
  int m = L1getComponents(base, components);
  for (int i = 0; i < m; i++) {
    BLOCK b1 = L1getBlock(components[i]);
    int j = L1toTD(b1, td);
    L1addTDEdge(k, j, td);
  }
  return k;
}

TD* L1decomposeGraph(GRAPH* graph) {
#ifdef VERBOSE
  clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &start);
#endif

  n = graph->n;
  if (n == 64) {
    all = -1ll;
  }
  else {
    all = (1llu << n) - 1;
  }

  neighborSets = (LONG*) malloc(sizeof(LONG) * n);
  for (int v = 0; v < n; v++) {
    neighborSets[v] = 0;
  }
  for (int v = 0; v < n; v++) {
    for (int i = 0; i < graph->vertices[v].degree; i++) {
      int w = graph->vertices[v].neighbors[i];
      neighborSets[v] |= 1llu << w;
      neighborSets[w] |= 1llu << v;
    }
  }

  L1allocate();
  L1decompose();

  TD* td = (TD*) malloc(sizeof(TD));
  td->nBag = 0;
  td->nEdge = 0;
  td->width = targetWidth;
  td->bags = (BAG*) malloc(sizeof(BAG) * n);
  td->edges = (TDEDGE*)malloc(sizeof(TDEDGE) * n);

  // necessary for freeing later
  for (int i = 0; i < n; i++) {
    td->bags[i].vertices = NULL;
  }

  LONG s = all & ~blocks[solution].component;
  if (s != 0) {
   int  k = L1addBag(s, td);
   int j = L1toTD(blocks[solution], td);
   L1addTDEdge(k, j, td);
  }
  else {
    L1toTD(blocks[solution], td);
  }
  L1deallocate();
  free(neighborSets);
  return td;
}

