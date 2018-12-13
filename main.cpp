#include <gmpxx.h>
#include <iostream>
#include <math.h>
#include "PBC.h"

using namespace std;

//Function Prototypes
mpz_class* getPrimes(int);
G1* gsArrayGen(unsigned int, Pairing*, G1*);
G2* gsArrayGen(unsigned int, Pairing*, G2*);
//Global variables


struct edge{
  unsigned int src;
  unsigned int des;
  //src<des in edge representation to avoid double counting.
  //The prime labeling is accessed by looking up the prime_arr with the
  //corresponding index stored in (src/des).
};


mpz_class* getPrimes(int n)
{
  mpz_class *prime_arr = NULL;
  prime_arr = new mpz_class[n];

  if(n >= 1)
  {
      *(prime_arr)=2;
  }

  unsigned int i=3,count,c;
  bool isPrime;

  for(count = 1; count < n; i++)
  {
    isPrime = true;
    for(c=2; c <= sqrt(i); c++)
    {
        if(i%c == 0)
        {
          isPrime = false;
          break;
        }
    }
    if(isPrime)
    {
      count++;
      *(prime_arr + count-1) = i;
    }

    }
    return prime_arr;
}

bool edgeCompare(struct edge edge_1,struct edge edge_2)
{
  //returns true if the two edges being compared are the same
  if(edge_1.src == edge_2.src && edge_1.des == edge_2.des)
    return true;
  else
    return false;
}

bool edgePresent(struct edge* edge_list, unsigned int ecount, struct edge new_edge)
{
  //Checks whether an edge is present in the array edge_list
  for(unsigned int i = 0; i < ecount; i++)
  {
    if(edgeCompare(new_edge,*(edge_list + i)))
      return true;
  }

  return false;
}

struct edge* genSubgraph(unsigned int vertices, unsigned int edges)
{
  //Generates random edges with given number of vertices and edges
  //Initialising prng
  time_t t;
  srand((unsigned) time(&t));

  struct edge new_edge;
  struct edge* edge_list;
  edge_list = (struct edge*) malloc(edges * sizeof(struct edge));

  for(unsigned int ecount = 0; ecount < edges;)
  {
    new_edge.src = rand()%vertices;
    unsigned int temp_des = rand()%vertices;

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

void printEdges(struct edge* edge_list, unsigned int edges)
{
  for(int i = 0; i < edges; i++)
    cout<<"The "<<i<<"th edge is:" <<"("<<(edge_list + i)->src<<","<<(edge_list + i)->des<<")\n";
}

G1* gsArrayGen(unsigned int edges, Pairing* e, G1* g1, Zr* s)
{
  //Elements have been passed by reference since g1 and e have private elements which cannot be copied
  G1* gsarr;
  gsarr = new G1[edges];

  Zr temp_s(*e,(long int)1);

  for(int i = 0; i < edges; i++)
  {
    *(gsarr+i) =  (*g1)^temp_s;
    temp_s = temp_s*(*s);
  }

  return gsarr;
}

G2* gsArrayGen(unsigned int edges, Pairing* e, G2* g2, Zr* s)
{
  G2* gsarr;
  gsarr = new G2[edges];

  Zr temp_s(*e,(long int)1);

  for(int i = 0; i < edges; i++)
  {
    *(gsarr+i) =  (*g2)^temp_s;
    temp_s = temp_s*(*s);
  }

  return gsarr;
}


int main(void)
{

  const unsigned int vertices = 20, edges = 10;
  const mpz_class *prime_arr = getPrimes(vertices);

  //Generating to disjoint Subgraphs
  const struct edge* E_1 = genSubgraph(vertices/2,edges);
  const struct edge* E_2 = genSubgraph(vertices/2,edges);

  //Setting pairing parameters
  const char *paramFileName = "a.param";
  FILE *sysParamFile = fopen(paramFileName, "r");
  if (sysParamFile == NULL) {
    cerr<<"Can't open the parameter file " << paramFileName << "\n";
    return 0;
  }

  Pairing e(sysParamFile);
  cout<<"Pairing Confirmation: "<< e.isPairingPresent()<< endl;
  cout<<"Symmetric Pairing: "<< e.isSymmetric()<< endl;
  fclose(sysParamFile);

  //Intialising generators to identity
  G1 g1(e,true);
  G2 g2(e,true);

  //Element from HASH. Nothing up my sleeve generators.
  g1 = G1(e, "Generator 1", 11);
  g1.dump(stdout,"g1 is");
  g2 = G2(e, "Generator 2", 11);
  g2.dump(stdout,"g2 is");

   //g2identity;
  GT(e,true).dump(stdout,"Identity in GT is");

  if(e(g1,g2) == GT(e,true))
  {
    cerr<<"Generators are degenerate. Exiting.";
    return 0;
  }

  //Public information array needed for making accumulators. This array would
  //be given to the prover and verifier by the trusted auditor.
  G1* gs1;
  G2* gs2;

  Zr s(e,true); //Auditor

  Zr temp(e,false);
  temp.dump(stdout,"Identity in Zr is:");
  //Random s chosen by the auditor. This cannot be revealed
  //to the verifier or the prover.

  gs1 = gsArrayGen(edges, &e, &g1, &s);//Auditor
  gs2 = gsArrayGen(edges, &e, &g2, &s);//Auditor

/*
  Polynomial Interpolation: We want the exponent to stay in Zr
  The accumulator accumulates values in Zr*. This is automatically satisfied
  since we choose our vetex identifiers as prime numbers. Moreover, we are
  guaranteed that acc_{E_1|2} != g^0 as long as acc_{E} != g^0. Incase the
  total accumulator is g^0, resampling s should make acc_E non-identity with
  high probability.
  Note also that the product of all vertex identifiers must be smaller than
  the order of the group for checking the gcd. This problem arises since
  when constructing the protocol for checking isolation, the definition of
  gcd used is over the entirety of nonnegative integers. However, the
  construction for accumulators is done with a finite cyclic group. Thus in
  order to "unify" the two, the cyclic group must seem infinite to the exponent
  i.e it must never exceed the modulus value. This is the price we pay for
  not having to check every edge pair in the two edge sets. One might be able
  "batch" the edge sets and gain some efficiency while using a small r but this
  would require multiple levels of bilinear pairings.
*/
}

/*
Code for debugging:
for(unsigned int i = 0;i < vertices;i++)
  cout<<"Prime "<<i<<" :"<<*(prime_arr + i)<<"\n";
for(int i = 0; i < edges; i++)
{
  cout<<"g1^(s^"<<i<<")";
  (gs1+i)->dump(stdout);
}

for(int i = 0; i < edges; i++)
{
  cout<<"g2^(s^"<<i<<")";
  (gs2+i)->dump(stdout);
}
*/
