
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <pbc.h>

#define true 1
#define false 0

struct edge{
  int src;
  int des;
  //src<des in vertex index.
};

int* getPrimes(int n)
{
  int *prime_arr;
  prime_arr = (int*) malloc(n * sizeof(int));

  if(n >= 1)
  {
      *(prime_arr) = 2;
  }

  int i = 3;
  _Bool isPrime;

  for(int count = 2; count <= n; i++)
  {
    isPrime = true;
      for(int c = 2; c <= sqrt(i); c++)
      {
          if(i%c == 0)
          {
            isPrime = false;
            break;
          }
      }
      if(isPrime)
      {
        *(prime_arr + count-1) = i;
        count++;
      }

    }
    return prime_arr;
}

_Bool edgeCompare(struct edge edge_1,struct edge edge_2)
{
  if(edge_1.src == edge_2.src && edge_1.des == edge_2.des)
    return true;
  else
    return false;
}

_Bool edgePresent(struct edge* edge_list, int ecount, struct edge new_edge)
{
  for(int i = 0; i < ecount; i++)
  {
    if(edgeCompare(new_edge,*(edge_list + i)))
      return true;
  }

  return false;
}

struct edge* genSubgraph(int vertices, int edges)
{
  //Initialising prng
  time_t t;
  srand((unsigned) time(&t));

  struct edge new_edge;
  struct edge* edge_list;
  edge_list = (struct edge*) malloc(edges * sizeof(struct edge));

  for(int ecount = 0; ecount < edges;)
  {
    new_edge.src = rand()%vertices;
    int temp_des = rand()%vertices;

    while(new_edge.src == temp_des)
      temp_des = rand()%vertices;

    if(temp_des < new_edge.src)
    {
      new_edge.des = new_edge.src;
      new_edge.src = temp_des;
    }
    else
      new_edge.des = temp_des;

    if(!edgePresent(edge_list, ecount, new_edge))
    {
      *(edge_list + ecount) = new_edge;
       ecount++;
    }
  }

  return edge_list;

}

void printEdges(struct edge* edge_list,int edges)
{
  for(int i = 0; i < edges; i++)
  {
    printf("The %dth edge is (%d, %d)\n",i,(edge_list + i)->src, (edge_list + i)->des);
  }
}

int main(void)
{
  int n = 100000;
  //int *prime_arr = getPrimes(n);
  //free(prime_arr);

  int vertices = 10, edges = 10;
  struct edge* E_1 = genSubgraph(vertices,edges);
  printEdges(E_1,edges);

  /*
  pairing_t pairing;
  char* s = "type a \n q 8780710799663312522437781984754049815806883199414208211028653399266475630880222957078625179422662221423155858769582317459277713367317481324925129998224791 \n h 12016012264891146079388821366740534204802954401251311822919615131047207289359704531102844802183906537786776 \n r 730750818665451621361119245571504901405976559617 \n exp2 159 \n exp1 107 \n sign1 1 \n sign0 1";
  pairing_init_set_str(pairing, s);


  element_t g, h;

  element_init_G2(g, pairing);
  element_init_G1(h, pairing);
  element_random(g);
  element_from_hash(h, "ABCDEF", 2);

  element_out_str(stdout, 10, g);
  printf("\n");
  printf("%d\n", pairing_is_symmetric(pairing));
  printf("%d\n", pairing_length_in_bytes_G1(pairing));
  printf("%d\n", pairing_length_in_bytes_G2(pairing));
  printf("%d\n", pairing_length_in_bytes_GT(pairing));
  printf("%d\n", pairing_length_in_bytes_Zr(pairing));
  element_random(g);
  /* call PBC functions */
  return 0;
}
