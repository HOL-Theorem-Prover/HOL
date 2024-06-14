/******************************************************************************************[Main.C]
MiniSat -- Copyright (c) 2003-2005, Niklas Een, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include "Solver.h"
#include <ctime>
#include <unistd.h>
#include <signal.h>
#include <iostream>
#include <fstream>

//=================================================================================================
// DIMACS Parser: // Inserts problem into solver.

using namespace std;

void addLit(int parsed_lit,Solver& S, vec<Lit>& lits) {
  int var = abs(parsed_lit)-1;
  while (var >= S.nVars()) S.newVar();
  lits.push( (parsed_lit > 0) ? Lit(var) : ~Lit(var) );
}

void addClause(Solver& S, vec<Lit>& lits) {
  /*for (int i=0;i<lits.size();i++)
    cout << (sign(lits[i]) ? "-" : "") << (var(lits[i])+1) << " ";
    cout << "#" << endl;*/
  S.addClause(lits);
  lits.clear();
}

static void parse_DIMACS(char* filename, Solver& S) {
  ifstream fin(filename);
  if (fin.fail()) { cerr << "Error opening input file " << filename << endl; exit(1); }  
  string line,stok;
  int itok;
  vec<Lit> lits;
  while(true) { // skip preamble (must have at least the p line)
    fin >> stok;
    if (stok=="c" || stok=="p") getline(fin,line);
    else break;
  }
  addLit(atoi(stok.c_str()),S,lits); // first lit of first clause
  while (true) {
    fin >> itok;
    if (fin.eof()) {
      if (lits.size()>0) addClause(S,lits); // in case last clause had no trailing 0
      break;
    }
    if (itok==0) addClause(S,lits);
    else addLit(itok,S,lits);          
  }
}
//=================================================================================================


void printStats(SolverStats& stats, double& cpu_time, int64& mem_used)
{
    cpu_time = cpuTime();
    mem_used = memUsed();
    reportf("restarts              : %" I64_fmt "\n", stats.starts);
    reportf("conflicts             : %-12" I64_fmt "   (%.0f /sec)\n", stats.conflicts   , stats.conflicts   /cpu_time);
    reportf("decisions             : %-12" I64_fmt "   (%.0f /sec)\n", stats.decisions   , stats.decisions   /cpu_time);
    reportf("propagations          : %-12" I64_fmt "   (%.0f /sec)\n", stats.propagations, stats.propagations/cpu_time);
    reportf("conflict literals     : %-12" I64_fmt "   (%4.2f %% deleted)\n", stats.tot_literals, (stats.max_literals - stats.tot_literals)*100 / (double)stats.max_literals);
    if (mem_used != 0) reportf("Memory used           : %.2f MB\n", mem_used / 1048576.0);
    reportf("CPU time              : %g s\n", cpu_time);
}

void printProofStats(double cpu_time, int64 mem_used) {
      double  cpu_time1 = cpuTime();
      int64   mem_used1 = memUsed();
      if (mem_used1!= 0) reportf("Extra memory used     : %.2f MB\n",
				 (mem_used1-mem_used)/1048576.0);
      reportf("Extra CPU time        : %g s\n", (cpu_time1-cpu_time));
}

Solver* solver;
static void SIGINT_handler(int signum) {
    reportf("\n"); reportf("*** INTERRUPTED ***\n");
    double cpu_time = 0;
    int64 mem_used = 0;
    printStats(solver->stats,cpu_time,mem_used);
    reportf("\n"); reportf("*** INTERRUPTED ***\n");
    exit(1); }


//=================================================================================================
// Simplistic proof-checker -- just to illustrate the use of 'ProofTraverser':


#include "Sort.h"

static void resolve(vec<Lit>& main, vec<Lit>& other, Var x)
{
    Lit     p;
    bool    ok1 = false, ok2 = false;
    for (int i = 0; i < main.size(); i++){
        if (var(main[i]) == x){
            ok1 = true, p = main[i];
            main[i] = main.last();
            main.pop();
            break;
        }
    }

    for (int i = 0; i < other.size(); i++){
        if (var(other[i]) != x)
            main.push(other[i]);
        else{
            if (!(p == ~other[i]))
                printf("PROOF ERROR! Resolved on variable with SAME polarity in both clauses: %d\n", x+1);
            ok2 = true;
        }
    }

    if (!ok1 || !ok2)
        printf("PROOF ERROR! Resolved on missing variable: %d\n", x+1);

    sortUnique(main);
}


struct Checker : public ProofTraverser {
    vec<vec<Lit> >  clauses;

    void root   (const vec<Lit>& c) {
        //**/printf("%d: ROOT", clauses.size()); 
        //for (int i = 0; i < c.size(); i++) 
        //   printf(" %s%d", sign(c[i])?"-":"", var(c[i])+1); 
        //printf("\n");
        clauses.push();
        c.copyTo(clauses.last()); }

    void chain  (const vec<ClauseId>& cs, const vec<Var>& xs) {
        //**/printf("%d: CHAIN %d", clauses.size(), cs[0]-1); 
        //for (int i = 0; i < xs.size(); i++) printf(" [%d] %d", (xs[i]>>1)+1, cs[i+1]-1);
        clauses.push();
        vec<Lit>& c = clauses.last();

	//HA: the -1 to compensate for id_counter base 1
	//HA: the >> 1 to drop sign info from vars
        clauses[cs[0]-1].copyTo(c); 
        for (int i = 0; i < xs.size(); i++) 
	  resolve(c, clauses[cs[i+1]-1], xs[i] >> 1); 
        //**/printf(" =>"); for (int i = 0; i < c.size(); i++) 
	//  printf(" %s%d", sign(c[i])?"-":"", var(c[i])+1); printf("\n");
        }

    void deleted(ClauseId c) {
        clauses[c].clear(); }
};


//HA: called with no second arg, so goal gets default value
void checkProof(Proof* proof, ClauseId goal = ClauseId_NULL)
{
    Checker trav;
    int res_count = 0;
    proof->traverse(trav, res_count, goal);
    printf("%d resolution steps.\n",res_count);
    vec<Lit>& c = trav.clauses.last();
    printf("Final clause:");
    if (c.size() == 0)
        printf(" <empty>\n");
    else{
        for (int i = 0; i < c.size(); i++)
            printf(" %s%d", sign(c[i])?"-":"", var(c[i])+1);
        printf("\n");
    }
}


//=================================================================================================
// Main:


static const char* doc =
    "USAGE: minisat <input-file> [options]\n"
    "  -r <result file>   Write result (the word \"SAT\" plus model, or just \"UNSAT\") to file.\n"
    "  -p <proof trace>   Write the trace to this file.\n"
    "  -c                 Check the trace by simple (read \"slow\") proof checker.\n"
    "  -x                 Extract proof from trace.\n"
;

int main(int argc, char** argv)
{
    char*       input  = NULL;
    char*       result = NULL;
    char*       proof  = NULL;
    bool        check  = false;
    bool        compress = false;

    // Parse options:
    //
    for (int i = 1; i < argc; i++){
        if (argv[i][0] != '-'){
            if (input != NULL)
                fprintf(stderr, "ERROR! Only one input file may be specified.\n"), exit(1);
            input = argv[i];
        }else{
            switch (argv[i][1]){
            case 'r':
                i++; if (i >= argc) fprintf(stderr, "ERROR! Missing filename after '-r' option.\n");
                result = argv[i];
                break;
            case 'p':
                i++; if (i >= argc) fprintf(stderr, "ERROR! Missing filename after '-p' option.\n");
                proof = argv[i];
                break;
            case 'c':
                check = true;
                break;
            case 'x':
	        compress = true; 
                break;
            case 'h':
                reportf("%s", doc);
                exit(0);
            default:
                fprintf(stderr, "ERROR! Invalid option: %s\n", argv[i]), exit(1);
            }
        }
    }

    // Parse input and perform SAT:
    //
    Solver      S;
    if (proof != NULL || check) S.proof = new Proof();
    if (input == NULL) { fprintf(stderr, "ERROR! Input file not specified"); exit(1); }
    parse_DIMACS(input, S);
   
    FILE*   res = (result != NULL) ? fopen(result, "wb") : NULL;

    if (!S.okay()){
        if (res != NULL) fprintf(res, "UNSAT\n"), fclose(res);
        if (S.proof != NULL && proof != NULL) S.proof->save(proof);
        if (S.proof != NULL && check) printf("Checking proof...\n"), checkProof(S.proof);
        reportf("Trivial problem\n");
        reportf("UNSATISFIABLE\n");
        exit(20);
    }

    S.verbosity = 1;
    solver = &S;
    signal(SIGINT,SIGINT_handler);
    signal(SIGHUP,SIGINT_handler);

    S.solve();

    double cpu_time = 0; int64 mem_used = 0;
    printStats(S.stats,cpu_time,mem_used);
    reportf("\n");
    reportf(S.okay() ? "SATISFIABLE\n" : "UNSATISFIABLE\n");

    if (res != NULL){
        if (S.okay()){
            fprintf(res, "SAT\n");
            for (int i = 0; i < S.nVars(); i++)
                if (S.model[i] != l_Undef)
                    fprintf(res, "%s%s%d", (i==0)?"":" ", (S.model[i]==l_True)?"":"-", i+1);
            fprintf(res, " 0\n");
        }else
            fprintf(res, "UNSAT\n");
        fclose(res);
    }

    // Post-processing of proof in case of UNSAT
    if (S.proof != NULL && !S.okay()){
      if (compress) { // ...compress, and possibly check
	reportf("Compressing proof...\n");
	Proof compressed;
	S.proof->compress(compressed,S.proof->last());
	if (check)
	  reportf("Checking compressed proof...\n"),
	    checkProof(&compressed);
	if (proof != NULL) compressed.save(proof);
	printProofStats(cpu_time,mem_used);
      } else if (check) { // ...check
	reportf("Checking proof...\n"),
	  checkProof(S.proof);
	if (proof != NULL) S.proof->save(proof);
	printProofStats(cpu_time,mem_used);	  
      } else if (proof != NULL) S.proof->save(proof);
    }
    
    // (faster than "return", which will invoke the destructor for 'Solver')
    exit(S.okay() ? 10 : 20);
				
}
