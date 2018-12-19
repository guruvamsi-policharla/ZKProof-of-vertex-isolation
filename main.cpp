#include <gmpxx.h>
#include <iostream>
#include <math.h>
#include "PBC.h"
#include <string.h>
#include "picosha2.h"
using namespace std;

//Function Prototypes
//Global variables

struct edge{
  unsigned int src;
  unsigned int des;
  mpz_class prod;
/*
  src<des in edge representation to avoid double counting.
  The prime labeling is accessed by looking up the prime_arr with the
  corresponding index stored in (src/des). Product of prime labels stored in
  prod.
*/
};

struct zkproof{
  Zr *c;
  unsigned int c_count;
  Zr *s;
  unsigned int s_count;
};

mpz_class* getPrimes(int n)
{
  //Returns an array of first n primes
  mpz_class *prime_arr = new mpz_class[n];

  if(n >= 1)
  {
      *(prime_arr)=2;
  }

  mpz_class i = 3,c;
  unsigned int count;
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
  //Returns true if the edges sent are the same
  if(edge_1.src == edge_2.src && edge_1.des == edge_2.des)
    return true;
  else
    return false;
}

bool edgePresent(const struct edge *edge_list, unsigned int ecount,
  struct edge new_edge)
{
  //Checks whether an edge is present in the array edge_list
  for(unsigned int i = 0; i < ecount; i++)
  {
    if(edgeCompare(new_edge,*(edge_list + i)))
      return true;
  }

  return false;
}

struct edge* genSubgraph(const unsigned int vertices, const unsigned int edges,
  const mpz_class *prime_arr, unsigned int vShift)
{
  //Generates random edges with given number of vertices and edges

  time_t t;
  srand((unsigned) time(&t));

  struct edge new_edge;
  struct edge* edge_list;
  edge_list = (struct edge*) malloc(edges * sizeof(struct edge));

  for(unsigned int ecount = 0; ecount < edges;)
  {
    new_edge.src = rand()%vertices + vShift;
    unsigned int temp_des = rand()%vertices + vShift;

    while(new_edge.src == temp_des)
      temp_des = rand()%vertices + vShift;

    if(temp_des < new_edge.src)
    {
      new_edge.des = new_edge.src;
      new_edge.src = temp_des;
    }

    else
      new_edge.des = temp_des;

    new_edge.prod = prime_arr[new_edge.src]*prime_arr[new_edge.des];

    if(!edgePresent(edge_list, ecount, new_edge))
    {
      *(edge_list + ecount) = new_edge;
       ecount++;
    }
  }

  return edge_list;
}

struct edge* joinGraphs(const unsigned int edges1, const unsigned int edges2,
  const struct edge* E_1, const struct edge* E_2)
{
  unsigned int edges = edges1 + edges2;
  struct edge new_edge;
  struct edge* edge_list;
  edge_list = new edge[edges];

  for(unsigned int i = 0; i < edges1; i++)
    edge_list[i] = E_1[i];
  for(unsigned int i = 0; i < edges2; i++)
    edge_list[i + edges1] = E_2[i];

  return edge_list;
}

void printEdges(const struct edge *edge_list, const unsigned int edges)
{
  //Prints edges from the given edge list
  for(int i = 0; i < edges; i++)
    cout<<"The "<<i<<"th edge is:" <<"("<<(edge_list + i)->src
    <<","<<(edge_list + i)->des<<","<<(edge_list + i)->prod<<")\n";
}

G1* gsArrayGen(const unsigned int edges1, Pairing *e, G1 *g1, Zr *s)
{
  //Elements have been passed by reference since g1 and e have private elements
  //which cannot be copied
  G1* gsarr;
  gsarr = new G1[edges1 + 1];

  Zr temp_s(*e,(long int)1);

  for(int i = 0; i < edges1 + 1; i++)
  {
    *(gsarr+i) =  (*g1)^temp_s;
    temp_s = temp_s*(*s);
  }

  return gsarr;
}

G2* gsArrayGen(const unsigned int edges2, Pairing *e, G2 *g2, Zr *s)
{
  G2* gsarr;
  gsarr = new G2[edges2 + 1];

  Zr temp_s(*e,(long int)1);

  for(int i = 0; i < edges2 + 1; i++)
  {
    *(gsarr+i) =  (*g2)^temp_s;
    temp_s = temp_s*(*s);
  }

  return gsarr;
}

void postfix(mpz_class *a, unsigned int n)
{
  //Used for interpolation by polyCoeff
  for(unsigned int i = n - 1; i > 0; i--)
    *(a + i - 1) = *(a + i - 1) + *(a + i);
}

void update(mpz_class *a, const struct edge *b, unsigned int n)
{
  //Used for interpolation by polyCoeffs
  for(unsigned int i = 1; i < n; i++)
    *(a + i - 1) = (b + i - 1)->prod * *(a + i);
}

Zr* polyCoeff(const struct edge* edge_list, const unsigned int edges,
Pairing *e)
{
  //Returns an array of polynomial coeffiecents when the input is the constant
  //terms as in the acc product(a,b,c,..) where (x+a)(x+b)(x+c)... is the
  //polynomial.
  mpz_class sum = 0;
  mpz_class *pcoeff_arr = new mpz_class[edges+1];
  mpz_class *temp_prod = new mpz_class[edges];

  for(unsigned int i = 0; i < edges; i++)
    *(temp_prod + i) = (edge_list + i)->prod;

  *(pcoeff_arr) = 1;//Coefficient of s^edges
  for(unsigned int i = 0; i < edges; i++)
    sum += *(temp_prod + i);

  *(pcoeff_arr + 1) = sum;//Coefficient of s^(edges-1)

  for(unsigned int i = 1; i < edges; i++)
  {
    postfix(temp_prod, edges - i + 1);

    sum = 0;

    for (unsigned int j = 1; j <= edges - i; j++)
      sum += ((edge_list + j - 1)->prod * *(temp_prod + j));

    *(pcoeff_arr + i + 1) = sum;

  	update(temp_prod, edge_list, edges);
  }

  //Conversion to Zr
  Zr* pcoeff_arrZr = new Zr[edges+1];

  for(unsigned int i = 0; i < edges + 1; i++)
  {
    //Initialising Zr with mpz_t
    Zr temp_Zr(*e,(pcoeff_arr+i)->get_mpz_t());
    *(pcoeff_arrZr + i) = temp_Zr;
  }

  return pcoeff_arrZr;
}

G1 accumulate(const unsigned int edges1, Zr *pcoeff_E1, G1 *gs1, Pairing *e)
{
  //Creates the accumulator when given an edge set and generator in g1
  G1 accE_1(*e,true);
  for(int i = 0; i < edges1 + 1; i++)
  {
    accE_1 = accE_1 * (gs1[i]^pcoeff_E1[edges1 - i]);
  }

  return accE_1;
}

G2 accumulate(const unsigned int edges2, Zr *pcoeff_E2, G2 *gs2, Pairing *e)
{
  //Creates the accumulator when given an edge set and generator in g2
  G2 accE_2(*e,true);
  for(int i = 0; i < edges2 + 1; i++)
  {
    accE_2 = accE_2 * (gs2[i]^pcoeff_E2[edges2 - i]);
  }

  return accE_2;
}

struct zkproof* SPK1(Zr *x, G1 *y, char *m, G1 *g1, Pairing *e)
{
  Zr r(*e,true);
  G1 t(*e,true);
  Zr c(*e,false);
  Zr s(*e,false);


  char temp_string[1000]; //TODO: Automate this length
  char hash_inp[10000];
  strcpy(hash_inp,"");

  element_snprintf(temp_string, 1000, "%B", g1);
  strcat(hash_inp,temp_string);

  element_snprintf(temp_string, 1000, "%B", y);
  strcat(hash_inp,temp_string);

  t = (*g1)^r;
  element_snprintf(temp_string, 1000, "%B", t);
  strcat(hash_inp,temp_string);

  strcat(hash_inp,m);//FIx this by using a SHA256 first maybe?
  //cout<<hash_inp<<endl;

  string hash_inp_str = string(hash_inp);
  char sha_outp[64];
  strcpy(sha_outp,picosha2::hash256_hex_string(hash_inp_str).c_str());

  c = Zr(*e,sha_outp,strlen(sha_outp));

  s = r - (c*(*x));

  struct zkproof *p1 = new zkproof[1];
  p1->c_count = 1;
  p1->c = new Zr[1];
  *(p1->c) = c;
  p1->s = new Zr[1];
  p1->s_count = 1;
  *(p1->s) = s;
  return p1;

}

struct zkproof* SPK1(Zr *x, G2 *y, char *m, G2 *g2, Pairing *e)
{
  Zr r(*e,true);
  G2 t(*e,true);
  Zr c(*e,false);
  Zr s(*e,false);


  char temp_string[1000]; //TODO: Automate this length
  char hash_inp[10000];
  strcpy(hash_inp,"");

  element_snprintf(temp_string, 1000, "%B", g2);
  strcat(hash_inp,temp_string);

  element_snprintf(temp_string, 1000, "%B", y);
  strcat(hash_inp,temp_string);

  t = (*g2)^r;
  element_snprintf(temp_string, 1000, "%B", t);
  strcat(hash_inp,temp_string);

  strcat(hash_inp,m);//FIx this by using a SHA256 first maybe?
  //cout<<hash_inp<<endl;

  string hash_inp_str = string(hash_inp);
  char sha_outp[64];
  strcpy(sha_outp,picosha2::hash256_hex_string(hash_inp_str).c_str());

  c = Zr(*e,sha_outp,strlen(sha_outp));

  s = r - (c*(*x));

  struct zkproof *p1 = new zkproof[1];
  p1->c_count = 1;
  p1->c = new Zr[1];
  *(p1->c) = c;
  p1->s = new Zr[1];
  p1->s_count = 1;
  *(p1->s) = s;
  return p1;

}

struct zkproof* SPK2(Zr *x, G1 *y, char *m, G1 *gs1, unsigned int k, Pairing *e)
{
  //Zr r_temp(*e,true);
  G1 t(*e,true);
  Zr *s = new Zr[k];
  Zr c(*e,false);
  Zr *r = new Zr[k];
  for(unsigned int i = 0; i < k; i++)
  {
    r[i] = Zr(*e,true);
  }

  char temp_string[1000]; //TODO: Automate this length
  char hash_inp[10000];
  strcpy(hash_inp,"");

  for(unsigned int i = 0; i < k; i++)
  {
    element_snprintf(temp_string, 1000, "%B", gs1 + i);
    strcat(hash_inp,temp_string);
  }

  element_snprintf(temp_string, 1000, "%B", y);
  strcat(hash_inp,temp_string);

  for(unsigned int i = 0; i < k; i++)
  {
    t *= (gs1[i])^r[i];
  }

  element_snprintf(temp_string, 1000, "%B", t);
  strcat(hash_inp,temp_string);

  strcat(hash_inp,m);

  string hash_inp_str = string(hash_inp);
  char sha_outp[64];
  strcpy(sha_outp,picosha2::hash256_hex_string(hash_inp_str).c_str());

  c = Zr(*e,sha_outp,strlen(sha_outp));

  for(unsigned int i = 0; i < k; i++)
  {
    s[i] = r[i] - c*(x[i]);
  }

  struct zkproof *p2 = new zkproof[1];
  p2->c_count = 1;
  p2->c = new Zr[1];
  p2->c[0] = c;
  p2->s_count = k;
  p2->s = new Zr[p2->s_count];

  for(unsigned int i = 0; i < p2->s_count; i++)
  {
    p2->s[i] = s[i];
  }

  return p2;
}

struct zkproof* SPK7(Zr *x_arr, G1 *y_arr, unsigned int y_count, char *m,
  G1 *g1_basis, unsigned int g1_count, unsigned int k, unsigned int u, Pairing *e)
{
  //g1_count is size of g1_basis
  //u is number of different exponents i.e size of x_arr
  G1 t1(*e,true);
  G1 t2(*e,true);
  Zr *s = new Zr[u];
  Zr c(*e,false);
  Zr *r = new Zr[u];
  for(unsigned int i = 0; i < u; i++)
  {
    r[i] = Zr(*e,true);
  }

  char temp_string[1000]; //TODO: Automate this length
  char hash_inp[10000];
  strcpy(hash_inp,"");

  //basis feed
  for(unsigned int i = 0; i < g1_count; i++)
  {
    element_snprintf(temp_string, 1000, "%B", g1_basis + i);
    strcat(hash_inp,temp_string);
  }

  //y_arr feed
  for(unsigned int i = 0; i < y_count; i++)
  {
    element_snprintf(temp_string, 1000, "%B", y_arr + i);
    strcat(hash_inp,temp_string);
  }

  //J feed
  for(unsigned int i = 0; i < g1_count-1; i++)
  {
    element_snprintf(temp_string, 1000, "%d,", i);
    strcat(hash_inp,temp_string);
  }
  //Concatenating S_1
    element_snprintf(temp_string, 1000, "%d|", g1_count-1);
    strcat(hash_inp,temp_string);
  //Concatenating g1
    element_snprintf(temp_string, 1000, "%d,", 0);
    strcat(hash_inp,temp_string);
  //Concatenating S_1
    element_snprintf(temp_string, 1000, "%d|", g1_count-1);
    strcat(hash_inp,temp_string);

  //e feed
  for(unsigned int i = 0; i < g1_count-1; i++)
  {
    element_snprintf(temp_string, 1000, "%d,", i);
    strcat(hash_inp,temp_string);
  }
  //Concatenating S_1
    element_snprintf(temp_string, 1000, "%d|", g1_count-1);
    strcat(hash_inp,temp_string);
  //Concatenating g1
    element_snprintf(temp_string, 1000, "%d,", 0);
    strcat(hash_inp,temp_string);
  //Concatenating S_1
    element_snprintf(temp_string, 1000, "%d|", g1_count-1);
    strcat(hash_inp,temp_string);

  //V feed

  for(unsigned int i = 0; i < g1_count; i++)
  {
    t1 *= (g1_basis[i])^r[i];
  }

  element_snprintf(temp_string, 1000, "%B", t1);
  strcat(hash_inp,temp_string);

    t2 = (g1_basis[0])^r[0];
    t2 *= (g1_basis[g1_count-1])^r[u-1];

  element_snprintf(temp_string, 1000, "%B", t2);
  strcat(hash_inp,temp_string);

  strcat(hash_inp,m);

  //cout<<hash_inp<<endl;

  string hash_inp_str = string(hash_inp);
  char sha_outp[64];
  strcpy(sha_outp,picosha2::hash256_hex_string(hash_inp_str).c_str());

  c = Zr(*e,sha_outp,strlen(sha_outp));

  for(unsigned int i = 0; i < u-1; i++)
  {
    s[i] = r[i] - c*(x_arr[i]);
  }

    s[u-1] = r[u-1] - c*(x_arr[u]);

  struct zkproof *p7 = new zkproof[1];
  p7->c_count = 1;
  p7->c = new Zr[1];
  p7->c[0] = c;

  p7->s_count = u;
  p7->s = new Zr[p7->s_count];
  for(unsigned int i = 0; i < p7->s_count; i++)
  {
    p7->s[i] = s[i];
  }

  return p7;

}

int main(void)
{
  unsigned int topo = 5;
  const unsigned int vertices1 = topo, vertices2 = topo, edges1 = topo, edges2 = topo;//Prover
  const unsigned int vertices = vertices1 + vertices2, edges = edges1 + edges2;//Prover
  const mpz_class *prime_arr = getPrimes(vertices);//Prover

  //Generating to disjoint Subgraphs
  const struct edge *E_1 = genSubgraph(vertices1, edges1, prime_arr, 0);//Prover
  const struct edge *E_2 = genSubgraph(vertices2, edges2, prime_arr, vertices1);//Prover
  const struct edge *E = joinGraphs(edges1, edges2, E_1, E_2);

  mpz_class edge_prod = 1;

  for(unsigned int i = 0; i < edges1; i++)
    edge_prod = edge_prod * E_1[i].prod;

  for(unsigned int i = 0; i < edges2; i++)
    edge_prod = edge_prod * E_2[i].prod;


  cout<<"Size of the constant term in the polynomial is : "<<
  mpz_sizeinbase(edge_prod.get_mpz_t(), 2)/8.0<<endl;

  //for(unsigned int i = 0; i < vertices; i++)
    //cout<<"Prime "<<i<<" :"<<*(prime_arr + i)<<"\n";

  //printEdges(E_1,edges1);
  //printEdges(E_2,edges2);
  //printEdges(E,edges);
  //Setting pairing parameters
  //Since there is no C++ parameter file generator, I am currently
  //writing the parameters to a file "my a.param" first and then
  //reading from the same using the C++ parameter init function
  pbc_param_t par;
  pbc_param_init_a_gen(par, 160, 512);


  pairing_t e_temp;
  pairing_init_pbc_param(e_temp, par);
  cout<<"Size of Zr : "<<pairing_length_in_bytes_Zr(e_temp)<<endl;

  if(pairing_length_in_bytes_Zr(e_temp)<mpz_sizeinbase(edge_prod.get_mpz_t(), 2)/8.0)
  {
    cerr<<"Size of Zr is too small. Increase size of r or decrease number of edges/vertices."
    <<endl;
    return 0;
  }

  const char *paramFileName = "my a.param";
  FILE *sysParamFile = fopen(paramFileName, "w");
  pbc_param_out_str(sysParamFile, par);
  fclose(sysParamFile);

  sysParamFile = fopen(paramFileName, "r");
  if (sysParamFile == NULL) {
    cerr<<"Can't open the parameter file " << paramFileName << "\n";
    return 0;
  }
  Pairing e(sysParamFile);
  //cout<<e.get_pbc_param_t();
  fclose(sysParamFile);
  //cout<<"Pairing Confirmation: "<< e.isPairingPresent()<< endl;
  //cout<<"Symmetric Pairing: "<< e.isSymmetric()<< endl;

  G1 g1(e,true);
  G2 g2(e,true);
  //Element from HASH. Nothing up my sleeve generators.
  g1 = G1(e, "Generator 1", 11);//All
  //g1.dump(stdout,"Generator 1 - g1 is");
  g2 = G2(e, "Generator 2", 11);//All
  //g2.dump(stdout,"Generator 2 - g2 is");

  if(e(g1,g2) == GT(e,true))
  {
    cerr<<"Generators are degenerate. Exiting.";
    return 0;
  }

  //Public information array needed for making accumulators. This array would
  //be given to the prover and verifier by the trusted auditor.
  G1* gs;
  G1* gs1;
  G2* gs2;

  Zr s(e,true); //Auditor. Random s chosen by the auditor. This cannot be
  //revealed to the verifier or the prover.

  gs = gsArrayGen(edges, &e, &g1, &s);//Auditor
  gs1 = gsArrayGen(edges1, &e, &g1, &s);//Auditor
  gs2 = gsArrayGen(edges2, &e, &g2, &s);//Auditor

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

  Zr *pcoeff_E;
  Zr *pcoeff_E1;
  Zr *pcoeff_E2;

  pcoeff_E = polyCoeff(E, edges, &e);//Prover
  pcoeff_E1 = polyCoeff(E_1, edges1, &e);//Prover
  pcoeff_E2 = polyCoeff(E_2, edges2, &e);//Prover

  G1 accE(e,true);
  G1 accE_1(e,true);
  G2 accE_2(e,true);

  accE = accumulate(edges, pcoeff_E, gs, &e);//Prover,Auditor
  accE_1 = accumulate(edges1, pcoeff_E1, gs1, &e);//Prover
  accE_2 = accumulate(edges2, pcoeff_E2, gs2, &e);//Prover

  //Commitments setup
  G1 S1(e,true);
  G2 S2(e,true);

  S1 = G1(e, "Blinding factor 1", 17);//All
  S2 = G2(e, "Blinding factor 2", 17);//All

  //Commitments
  Zr r_E(e,true);
  Zr r_E_1(e,true);
  Zr r_E_2(e,true);
  Zr r_rho_1(e,true);
  Zr r_rho_2(e,true);

  G1 C_E(e,true);
  G1 C_E_1(e,true);
  G1 C_rho_1(e,true);
  G2 C_E_2(e,true);
  G2 C_rho_2(e,true);

  C_E = accE * S1^r_E;//Prover
  C_E_1 = accE_1 * S1^r_E_1;//Prover
  C_rho_1 = (g1^pcoeff_E1[edges1]) * (S1^r_rho_1);
  //There seems to be an issue in deciding precedence without brackets
  C_rho_2 = (g2^pcoeff_E2[edges2]) * (S2^r_rho_2);
  C_E_2 = accE_2 * S2^r_E_2;//Prover

  ////////////////////////////////////////////////////////////////Setup Complete

  /////////////////////////////////////////////////////////////////////SPK1 test
  Zr x(e,true);
  G1 y(e,false);
  y = (g1^x);
  char m[1000];
  strcpy(m,"Test String");
  struct zkproof *p1 = SPK1(&x, &y, m, &g1, &e);
  //----------------------------------------------------------------------------
  G1 V(e,false);
  Zr c(e,true);

  char temp_string[1000]; //TODO: Automate this length
  char hash_inp[10000];
  strcpy(hash_inp,"");

  element_snprintf(temp_string, 10000, "%B", g1);
  strcat(hash_inp,temp_string);

  element_snprintf(temp_string, 10000, "%B", y);
  strcat(hash_inp,temp_string);

  V = (g1^(p1->s[0])) * (y^(p1->c[0]));
  //V = (g1^(p1->c[0])) * (y^(p1->s[0]));
  element_snprintf(temp_string, 10000, "%B", V);
  strcat(hash_inp,temp_string);

  strcat(hash_inp,m);

  string hash_inp_str = string(hash_inp);
  char sha_outp[64];
  strcpy(sha_outp,picosha2::hash256_hex_string(hash_inp_str).c_str());

  c = Zr(e,sha_outp,strlen(sha_outp));

  //element_from_hash does not seem to be a secure cryptographic hash function
  //Hence bootstrapping with sha256 which seems to prevent false verifications
  //with higher probability.

  if(c == p1->c[0])
    cout<<"SPK1 Verified"<<endl;
  else
    cout<<"SPK1 Verification Failed"<<endl;


  ////////////////////////////////////////////////////SPK1 verification complete

  /////////////////////////////////////////////////////////////////////SPK2 test
  Zr *x_arr = new Zr[edges1 + 1];
  y = G1(e,true);

  for(unsigned int i = 0; i < edges1 + 1; i++)
  {
    x_arr[i] = Zr(e,true);
    y *= gs1[i]^x_arr[i];
  }

  strcpy(hash_inp,"");
  strcpy(m,"Test String");
  struct zkproof *p2 = SPK2(x_arr, &y, m, gs1, edges1 + 1, &e);

  for(unsigned int i = 0; i < edges1 + 1; i++)
  {
    element_snprintf(temp_string, 1000, "%B", gs1 + i);
    strcat(hash_inp,temp_string);
  }

  element_snprintf(temp_string, 1000, "%B", y);
  strcat(hash_inp,temp_string);

  V = G1(e,true);
  V = (y^p2->c[0]);
  for(unsigned int i = 0; i < edges1 + 1; i++)
  {
    V *= gs1[i]^(p2->s[i]);
  }

  element_snprintf(temp_string, 1000, "%B", V);
  strcat(hash_inp,temp_string);

  strcat(hash_inp,m);

  hash_inp_str = string(hash_inp);
  strcpy(sha_outp,picosha2::hash256_hex_string(hash_inp_str).c_str());

  c = Zr(e,sha_outp,strlen(sha_outp));

  if(c == p2->c[0])
    cout<<"SPK2 Verified"<<endl;
  else
    cout<<"SPK2 Verification Failed"<<endl;

  ////////////////////////////////////////////////////SPK2 verification complete

  /////////////////////////////////////////////////////////////////////SPK7 test
  delete[] x_arr;

  x_arr = new Zr[edges1 + 1 + 3];//2 S1s extra and one g1
  G1 *y_arr = new G1[2];
  y = G1(e,true);

  G1 *g1_basis = new G1[edges1 + 1 + 1];//S1 extra added

  unsigned int g1_count = edges1 + 2;
  unsigned int y_count = 2;

  for(unsigned int i = 0; i < edges1 + 1; i++)
  {
    g1_basis[i] = gs1[i];
  }

  g1_basis[edges1+1] = S1;

  for(unsigned int i = 0; i < edges1 + 2; i++)
  {
    x_arr[i] = Zr(e,true);
  }

    x_arr[edges1 + 2] = x_arr[0];
    x_arr[edges1 + 3] = Zr(e,true);

  for(unsigned int i = 0; i < edges1 + 2; i++)
  {
    y *= g1_basis[i]^x_arr[i];
  }
  y_arr[0] = y;

  y = G1(e,true);

    y *= g1_basis[0]^x_arr[0];
    y *= g1_basis[g1_count - 1]^x_arr[edges1 + 3];

  y_arr[1] = y;

  strcpy(hash_inp,"");
  strcpy(m,"Test String");
  struct zkproof *p7 = SPK7(x_arr, y_arr, 2, m, g1_basis, edges1 + 2,
     edges1 + 4, edges1 + 3, &e);

  ////////////////////////Verification
  for(unsigned int i = 0; i < g1_count; i++)
  {
    element_snprintf(temp_string, 1000, "%B", g1_basis + i);
    strcat(hash_inp,temp_string);
  }

  //y_arr feed
  for(unsigned int i = 0; i < y_count; i++)
  {
    element_snprintf(temp_string, 1000, "%B", y_arr + i);
    strcat(hash_inp,temp_string);
  }

  //J feed
  for(unsigned int i = 0; i < g1_count-1; i++)
  {
    element_snprintf(temp_string, 1000, "%d,", i);
    strcat(hash_inp,temp_string);
  }
  //Concatenating S_1
    element_snprintf(temp_string, 1000, "%d|", g1_count-1);
    strcat(hash_inp,temp_string);
  //Concatenating g1
    element_snprintf(temp_string, 1000, "%d,", 0);
    strcat(hash_inp,temp_string);
  //Concatenating S_1
    element_snprintf(temp_string, 1000, "%d|", g1_count-1);
    strcat(hash_inp,temp_string);

  //e feed
  for(unsigned int i = 0; i < g1_count-1; i++)
  {
    element_snprintf(temp_string, 1000, "%d,", i);
    strcat(hash_inp,temp_string);
  }
  //Concatenating S_1
    element_snprintf(temp_string, 1000, "%d|", g1_count-1);
    strcat(hash_inp,temp_string);
  //Concatenating g1
    element_snprintf(temp_string, 1000, "%d,", 0);
    strcat(hash_inp,temp_string);
  //Concatenating S_1
    element_snprintf(temp_string, 1000, "%d|", g1_count-1);
    strcat(hash_inp,temp_string);

  V = G1(e,true);

  V *= y_arr[0]^p7->c[0];
  for(unsigned int i = 0; i < p7->s_count-1; i++)
  {
    V *= (g1_basis[i])^p7->s[i];
  }

  element_snprintf(temp_string, 1000, "%B", V);
  strcat(hash_inp,temp_string);

  V = G1(e,true);

  V = y_arr[1]^p7->c[0];

    V *= (g1_basis[0])^p7->s[0];
    V *= (g1_basis[g1_count-1])^p7->s[p7->s_count-1];

  element_snprintf(temp_string, 1000, "%B", V);
  strcat(hash_inp,temp_string);

  strcat(hash_inp,m);

  hash_inp_str = string(hash_inp);
  strcpy(sha_outp,picosha2::hash256_hex_string(hash_inp_str).c_str());

  c = Zr(e,sha_outp,strlen(sha_outp));

  if(c == p7->c[0])
    cout<<"SPK7 Verified"<<endl;
  else
    cout<<"SPK7 Verification Failed"<<endl;
  ////////////////////////////////////////////////////SPK7 verification complete

  
}

/*
Code for debugging:
for(unsigned int i = 0; i < edges1 + 1; i++)
  cout<<"E1 - Coeff of s^("<<edges1-i<<") :"<<*(pcoeff_E1 + i)<<"\n";

for(unsigned int i = 0; i < edges2 + 1; i++)
  cout<<"E2 - Coeff of s^("<<edges2-i<<") :"<<*(pcoeff_E2 + i)<<"\n";

for(unsigned int i = 0; i < vertices; i++)
  cout<<"Prime "<<i<<" :"<<*(prime_arr + i)<<"\n";

for(int i = 0; i < edges1; i++)
{
  cout<<"E1 - Coeff of s^("<<edges1-i<<") ";
  (pcoeff_E1+i)->dump(stdout,"",10);
}

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
