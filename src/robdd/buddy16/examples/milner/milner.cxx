#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>
#include "bdd.h"

int N;                // Number of cyclers
bdd normvar;          // Current state variables
bdd primvar;          // Next state variables
bddPair *renamepair;  // Variable pairs for renaming


bdd A(bdd* x, bdd* y, int z)
{
   bdd res = bddtrue;
   int i;
   
   for(i=0; i<N; i++)
      if(i != z)
	 res &= bdd_apply(x[i],y[i],bddop_biimp);
   
   return res;
}


bdd transitions(bdd* t, bdd* tp, bdd* h, bdd* hp, bdd* c, bdd* cp)
{
   int i;
   bdd P, E, T = bddfalse;
   
   for(i=0; i<N; i++)
   {
      P = ((c[i]>cp[i]) & (tp[i]>t[i]) & hp[i] & A(c,cp,i)
	   & A(t,tp,i) & A(h,hp,i))
	 | ((h[i]>hp[i]) & cp[(i+1)%N] & A(c,cp,(i+1)%N) & A(h,hp,i)
	    & A(t,tp,N));
      
      E = t[i] & !tp[i] & A(t,tp,i) & A(h,hp,N) & A(c,cp,N);
      
      T |= P | E;
   }
   
   return T;
}


bdd initial_state(bdd* t, bdd* h, bdd* c)
{
   int i;
   bdd I = c[0] & !h[0] & !t[0];
   
   for(i=1; i<N; i++)
      I &= !c[i] & !h[i] & !t[i];
   
   return I;
}


bdd reachable_states(bdd I, bdd T)
{
   bdd C, by, bx = I;

   //bdd_reorder(BDD_REORDER_SIFT);
      
   do
   {
      by = bx;

      //printf("C1:\n"); bdd_printset(C); printf("\n");
      
#if 0
      C = T & bx;
      //C = bdd_exist(C, renamepair, BDD_SETEQU);
      C = bdd_exist(C, normvar);
#else
      C = bdd_appex(bx, T, bddop_and, normvar);
      //C = bdd_appex(bx, T, bddop_and, renamepair, BDD_SETEQU);
#endif
      C = bdd_replace(C, renamepair);
      bx |= C;
      //printf("."); fflush(stdout);
   }
   while(bx != by);
   
   printf("\n");
   return bx;
}


int main(int argc, char** argv)
{
   int n;
   if(argc < 2)
   {
      printf("usage: milner N\n");
      printf("       N  number of cyclers\n");
      exit(1);
   }
   
   N = atoi(argv[1]);
   if (N <= 0)
   {
      printf("The number of cyclers must be more than zero\n");
      exit(2);
   }
   
   long clk1 = clock();
   
   bdd_init(100000, 10000);
   bdd_setvarnum(N*6);
   
   bdd* c  = new bdd[N];
   bdd* cp = new bdd[N];
   bdd* t  = new bdd[N];
   bdd* tp = new bdd[N];
   bdd* h  = new bdd[N];
   bdd* hp = new bdd[N];
   
   int *nvar = new int[N*3];
   int *pvar = new int[N*3];
   
   for (n=0 ; n<N*3 ; n++)
   {
      nvar[n] = n*2;
      pvar[n] = n*2+1;
   }
   
   normvar = bdd_makeset(nvar, N*3);
   primvar = bdd_makeset(pvar, N*3);
   renamepair = bdd_newpair();
   bdd_setpairs(renamepair, pvar, nvar, N*3);
   
   for (n=0 ; n<N ; n++)
   {
      c[n]  = bdd_ithvar(n*6);
      cp[n] = bdd_ithvar(n*6+1);
      t[n]  = bdd_ithvar(n*6+2);
      tp[n] = bdd_ithvar(n*6+3);
      h[n]  = bdd_ithvar(n*6+4);
      hp[n] = bdd_ithvar(n*6+5);
   }
   
   bdd I = initial_state(t,h,c);
   bdd T = transitions(t,tp,h,hp,c,cp);
   bdd R = reachable_states(I,T);
   
   long clk2 = clock();
   
   bddStat s;
   bdd_stats(&s);
   
   printf("SatCount R = %.0f\n", bdd_satcount(R));
   printf("Calc       = %.0f\n", (double)N*pow(2.0,1.0+N)*pow(2.0,3.0*N));
   printf("Nodes      = %ld\n", s.produced);
   printf("%.2f sec.\n", (float)(clk2 - clk1)/(float)(CLOCKS_PER_SEC));
   
   bdd_done();
   return 0;
}

