/* td.h */

typedef struct bag{
  int nv;
  int* vertices;
} BAG;

typedef struct td_edge{
  int b1;
  int b2;
} TDEDGE;

typedef struct treedecomposition{
  int nBag;
  int nEdge;
  int width;
  BAG* bags;
  TDEDGE* edges;
} TD;

TD* L1decomposeGraph(GRAPH* graph);
TD* L2decomposeGraph(GRAPH* graph);
TD* L4decomposeGraph(GRAPH* graph);
TD* L8decomposeGraph(GRAPH* graph);
TD* L16decomposeGraph(GRAPH* graph);
TD* L32decomposeGraph(GRAPH* graph);
TD* L64decomposeGraph(GRAPH* graph);
