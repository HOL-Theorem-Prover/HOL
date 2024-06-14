
#include <iostream>
#include <list>
#include <map>
#include <stack>
#include <set>
#include <vector>
#include <queue>
#include <ctime>
#include <unistd.h>
#include <signal.h>
#include "Global.h"
#include "Proof.h"
#include <fstream>
#include "Sort.h"
#include <string>
#include <sstream> 
#include<algorithm>
using namespace std;

enum enum_ty { ROOT, CL, VAR, CONF, DONE };
typedef vector<pair<enum_ty,vector<ClauseId> > > parsed_clauses; // if first=0,1,2,3 then root,CL,VAR,CONF


//=================================================================================================
// DIMACS Parser:

void vi2vl(const vector<int>& vi, vec<Lit>& vl) {
  int vsz = vi.size();
  for (int ii=0;ii<vsz;ii++) 
    vl.push(Lit(vi[ii]>>1,vi[ii]&1));
} 

void addLit(int parsed_lit,vector<int>& lits, int& numvars) {
  int var = abs(parsed_lit)-1;
  while (var >= numvars) numvars++;
  lits.push_back( (parsed_lit > 0) ? var+var : var+var+1 );
}

void addClause(vector<int>& lits, vec<vec<Lit> >& roots, parsed_clauses* pclauses, 
	       map<Lit,ClauseId>& units, int& numclauses) {
  bool skip = false;
  sort(lits.begin(),lits.end());
  lits.erase(unique(lits.begin(),lits.end()),lits.end()); //sortUnique(lits);  
  for (int i = 0; i < lits.size()-1; i++) // skip trivial clause
    if (lits[i] == ((lits[i+1])^1)) {
      skip=true;
      break;
    } 
  if (!skip) {
    if (lits.size()==1) 
      units.insert(make_pair(Lit(lits[0]>>1,lits[0]&1),numclauses));
    pclauses->push_back(make_pair(ROOT,lits));
    vec<Lit> Lits;
    vi2vl(lits,Lits);
    roots.push();
    Lits.copyTo(roots.last());
    numclauses++;	  
  }
  lits.clear();
}

void parse_DIMACS(Proof& P, vec<vec<Lit> >& roots, char* filename, parsed_clauses* pclauses,
			 map<Lit,ClauseId>& units, int& numvars, int& numclauses ) {
  ifstream fin(filename);
  if (fin.fail()) { cerr << "Error opening input file " << filename << endl; exit(1); }  
  string line,stok;
  int itok;
  vector<int> lits;
  while(true) { // skip preamble (must have at least the p line)
    fin >> stok;
    if (stok=="c" || stok=="p") getline(fin,line);
    else break;
  }
  addLit(atoi(stok.c_str()),lits,numvars); // first lit of first clause
  while (true) {
    fin >> itok;
    if (fin.eof()) {
      if (lits.size()>0) addClause(lits,roots,pclauses,units,numclauses); // in case last clause had no trailing 0
      break;
    }
    if (itok==0) addClause(lits,roots,pclauses,units,numclauses);
    else addLit(itok,lits,numvars);          
  }
}

//=========================================================================================================
// Simplistic proof-checker -- just to illustrate the use of 'ProofTraverser':

// Proof checker is from MiniSat 1.14p sources (MIT license reproduced below)
/*****************************************************************************************[Main.C]
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
  int res_count;
  Checker() { res_count = 0; }

    void root   (const vec<Lit>& c) {
      /*printf("%d: ROOT", clauses.size()); 
	for (int i = 0; i < c.size(); i++) 
	printf(" %s%d", sign(c[i])?"-":"", var(c[i])+1); printf("\n");*/
        clauses.push();
        c.copyTo(clauses.last()); }

    void chain  (const vec<ClauseId>& cs, const vec<Var>& xs) {
      /*printf("%d: CHAIN %d", clauses.size(), cs[0]-1); 
	for (int i = 0; i < xs.size(); i++) 
	printf(" [%d] %d", (xs[i]>>1)+1, cs[i+1]-1);*/
        clauses.push();
        vec<Lit>& c = clauses.last();
        clauses[cs[0]-1].copyTo(c);
	res_count+=xs.size();
        for (int i = 0; i < xs.size(); i++)
	  resolve(c, clauses[cs[i+1]-1], xs[i]>>1);
        /*printf(" =>"); for (int i = 0; i < c.size(); i++) 
	  printf(" %s%d", sign(c[i])?"-":"", var(c[i])+1); printf("\n");*/
        }

    void deleted(ClauseId c) {
        clauses[c].clear(); }
};


void checkProof(Proof* proof, ClauseId goal = ClauseId_NULL)
{
    Checker trav;
    proof->traverse(trav, goal);

    vec<Lit>& c = trav.clauses.last();
    printf("Final clause:");
    if (c.size() == 0)
        printf(" <empty>\n");
    else{
        for (int i = 0; i < c.size(); i++)
            printf(" %s%d", sign(c[i])?"-":"", var(c[i])+1);
        printf("\n");
    }
    printf("Inferences: %d\n",trav.res_count);
}
//MIT license ends here
//=================================================================================================


//==========================================================================================
// zChaff trace parsing
// Follows Tjark Weber's documentation of the zChaff proof format (TPHOLs2005, track B)

void parse_zChaff(char * filename, int& numclauses, 
		  parsed_clauses* pclauses, vector<int>& vars) {
  ifstream fin(filename);
  if (fin.fail()) { cerr << "Error opening zChaff trace file " << filename << endl; exit(0); }  
  istringstream iss;
  string line,stok;
  int itok;
  while (true) {
    getline(fin,line);
    iss.clear();
    iss.str(line);
    iss >> stok;
    if (stok=="CL:") {
      iss >> itok;  //clause id set by zChaff is ignored
      iss >> stok; assert(stok=="<=");
      vector<ClauseId> resolvents;
      while (!iss.eof()) {
	iss >> itok;
        resolvents.push_back(itok); 
      }
      pclauses->push_back(make_pair(CL,resolvents));
      numclauses++;
    }
    else if (stok=="VAR:") {      
      int vid; iss >> vid;
      iss >> stok; assert(stok=="L:");
      int level; iss >> level;
      iss >> stok; assert(stok=="V:");
      int value; iss >> value;
      assert((value ==0) || (value==1));
      iss >> stok; assert(stok=="A:");
      int ante; iss >> ante;
      // we don't parse the rest of the line
      vars[vid-1] = pclauses->size();
      vector<int> varv;
      varv.push_back(((vid-1)<<1)|(value?0:1));
      varv.push_back(ante);
      varv.push_back(level);
      pclauses->push_back(make_pair(VAR,varv));
      numclauses++;
    }
    else if (stok=="CONF:") {
      int conf_id; iss >> conf_id;
      // we don't parse the rest of the line
      vector<int> confv;
      confv.push_back(conf_id);
      pclauses->push_back(make_pair(CONF,confv));
      numclauses++;
      break;
    } else { cerr << "Unrecognized token\n"; exit(1); }
  }
}

//==========================================================================================

void printProofStats() {
      double  cpu_time = cpuTime();
      int64   mem_used = memUsed();
      if (mem_used!= 0) cout << "Memory used : " <<  ((mem_used)/1048576.0) << " MB" << endl;
      cout << "CPU time : " <<  cpu_time << " s" << endl;
}

//==========================================================================================
// zChaff to MiniSat translation functions 
// Follows Tjark Weber's documentation of the zChaff proof format (TPHOLs2005, track B)

class Z2M { 
  vector<int> vartmp;
  vector<int> lu;
  vector<int> c2c;
  Proof& P;
  vec<vec<Lit> >& clauses;
  vec<vec<Lit> >& roots;
  map<Lit,ClauseId>& units;
  vector<int>& vars;
  const int numclauses; // total number of clauses in trace
  const int numvars;
  parsed_clauses& pclauses;

  void update(vector<int>& ps, int lit, vector<int>& r1) {
    int flag = vartmp[lit>>1];
    if (flag==-1) { // lit not seen yet
      r1.push_back(lit); 
      vartmp[lit>>1] = lit; 
      lu.push_back(lit>>1); 
    } else if (flag==(lit^1)) { // seen and now seen with opp sign: piv "second" occ    
      vartmp[lit>>1]=lit; // switch vartmp to "second" occurrence
      ps.push_back(flag); // record pivot in ps
    } 
  }

  // calculate learnt clause, and fill in list of pivot vars
  void get_res(const vector<int>& resolvents,
	       vec<Lit>& res, vector<int>& ps) {
    vector<int> r1; 
    int rsz = resolvents.size();
    for (int ii=0;ii<rsz;ii++) {
      const vec<Lit>& cc = clauses[c2c[resolvents[ii]]];
      int csz = cc.size();
      for (int jj=0;jj<csz;jj++) 
	update(ps,index(cc[jj]),r1);    
    }
    int r1sz = r1.size();
    for (int ii=0;ii<r1sz;ii++) {
      int lit = r1[ii];
      if ((vartmp[lit>>1]^1)==lit) continue; // a "first" occ of pivot
      res.push(Lit(lit>>1,lit&1));
    }
    int lsz = lu.size();
    for (int ii=0;ii<lsz;ii++) vartmp[lu[ii]]=-1;
    lu.clear();
  }
  
  // create minisat chain for a "CL" line of zChaff proof trace
  int addChain(vector<int>& resolvents, int ci) {
    vec<Lit> res;
    vector<int> ps; // pivots
    get_res(resolvents,res,ps);
    assert(ps.size()==resolvents.size()-1);
    P.beginChain(c2c[resolvents[0]]+1); //+1 because modified Proof.C clause count is base 1
    for (int ii=1; ii<resolvents.size();ii++) {
      P.resolve(c2c[resolvents[ii]]+1, ~Lit(ps[ii-1]>>1,ps[ii-1]&1));
    } 
    int idx = P.endChain()-1; //-1 because zc2hs (and zchaff) clause count is base 0
    assert(idx==clauses.size());
    if (res.size()==1) 
      units.insert(make_pair(res[0],ci));
    clauses.push();
    res.copyTo(clauses.last());
    return idx;
  }
  
  // create minisat chain for a "VAR" line of zChaff proof trace
  // each lit in ante has a corresponding unit clause with opposing sign, 
  // which we can lookup via units
  // when all these unit clauses are resolved against the clause ante, 
  // we get a unit clause which is the same as var vid with sign sgn
  int addVChain(int vid, bool sgn, int ante, int ci) {
    vec<Lit>& lits = clauses[c2c[ante]];
    Lit p(vid,sgn);
    P.beginChain(c2c[ante]+1);
    for (int i=0; i<lits.size();i++) {
      if (lits[i]==p) continue; // skip vid itself
      // pick up unit clause id corresponding to -ve of lit
      map<Lit,ClauseId>::iterator iter = units.find(~lits[i]); 
      assert(iter!=units.end());
      P.resolve(c2c[iter->second]+1, ~lits[i]); 
    }
    int idx = P.endChain()-1;
    assert(idx==clauses.size());
    units.insert(make_pair(p,ci));
    clauses.push();
    clauses.last().push(p);
    return idx;
  }
  
  // create minisat chain for "CONF" line of zChaff proof trace
  // this is more or less the same as writeVChain, except
  // that instead of deriving a unit clause we derive empty
  void addCChain(int conf_id) {
    vec<Lit>& lits = clauses[c2c[conf_id]];
    P.beginChain(c2c[conf_id]+1);
    for (int i=0; i<lits.size();i++) {
      // pick up unit clause id corresponding to this lit
      map<Lit,ClauseId>::iterator iter = units.find(~lits[i]); 
      assert(iter!=units.end());
      P.resolve(c2c[iter->second]+1, ~lits[i]); 
    }
    P.endChain();
  }

  void addRoot(int ci) {
    clauses.push();
    roots[ci].copyTo(clauses.last());
    c2c[ci] = P.addRoot(clauses.last(),ci+1)-1;
    pclauses[ci].first=DONE;
  }

  void build_clause(int ci) {
    pair<enum_ty,vector<int> >& clause_info = pclauses[ci];    
    vector<int>& resolvents = clause_info.second;
    int rsz = resolvents.size();
    for (int ii=0;ii<rsz;ii++) 
      build(resolvents[ii]);
    c2c[ci] = addChain(resolvents,ci); // learnt    
    pclauses[ci].first=DONE;
  }

  void build_var(int ci) {
    pair<enum_ty,vector<int> >& clause_info = pclauses[ci];
    int lit = clause_info.second[0];
    int ante = clause_info.second[1];
    build(ante);
    if (clauses[c2c[ante]].size()==1) {
      pclauses[ci].first=DONE;
      return;
    }; 
    vec<Lit> cc;
    clauses[c2c[ante]].copyTo(cc);
    vector<pair<int,int> > levels;
    for (int ii=0;ii<cc.size();ii++) {
      if (lit==index(cc[ii])) continue; // skip lit of the var itself
      int ci = vars[var(cc[ii])];
      levels.push_back(make_pair(pclauses[ci].second[2],ci));
    }
    sort(levels.begin(),levels.end());
    for (int ii=0;ii<cc.size()-1;ii++) 
      build(levels[ii].second);
    c2c[ci] = addVChain(lit>>1, (bool)(lit&1), ante, ci);
    pclauses[ci].first=DONE;
  }

  // ci is index in pclauses
  void build(int ci) {
    switch (pclauses[ci].first) {
    case ROOT: addRoot(ci); break;
    case CL: build_clause(ci); break;
    case VAR: build_var(ci); break; 
    case DONE: break;
    default: cerr << "build default\n"; exit(1);
    }
  }

public: 

  Z2M(Proof& P_,vec<vec<Lit> >& clauses_,vec<vec<Lit> >& roots_,
      map<Lit,ClauseId>& units_, vector<int>& vars_, int numclauses_,
      int numvars_, parsed_clauses& pclauses_) :
    P(P_),
    clauses(clauses_),
    roots(roots_),
    units(units_),
    vars(vars_),numclauses(numclauses_),numvars(numvars_),
    pclauses(pclauses_),
    vartmp(numvars_,-1),
    c2c(pclauses_.size(),-1) {}

  void build_clauses() {
    pair<enum_ty,vector<int> >& clause_info = pclauses.back();  
    int conf_id = clause_info.second[0];
    build(conf_id);
    vec<Lit> cc;
    clauses[c2c[conf_id]].copyTo(cc);
    vector<pair<int,int> > levels;
    for (int ii=0;ii<cc.size();ii++) {
      int ci = vars[var(cc[ii])];
      levels.push_back(make_pair(pclauses[ci].second[2],ci));
    }
    sort(levels.begin(),levels.end());
    for (int ii=0;ii<cc.size();ii++) 
      build(levels[ii].second);
    addCChain(conf_id);  
  }

};

//==========================================================================================

int main(int argc, char** argv) {
  char*       input  = NULL; // the name of the input CNF problem file
  char*       proof  = NULL; // the name of the output minisat proof trace file
  char*       zchaff  = NULL; // the name of the input zChaff proof trace file
  bool        check  = false; // verify the proof if true
  static const char* doc =
    "USAGE: zc2hs input-cnf-file -z input-zchaff-trace -m output-holsat-trace [-c] \n";

  for (int i = 1; i < argc; i++) {
    if (argv[i][0] != '-') {
      if (input != NULL)
	fprintf(stderr, "ERROR! Only one input file may be specified.\n"), exit(1);
      input = argv[i];
    } else {
      switch (argv[i][1]){
      case 'c':
	check = true;
	break;
      case 'm': 
	i++; if (i >= argc) fprintf(stderr, "ERROR! Missing filename after '-m' option.\n");
	proof = argv[i];
	break;
      case 'z': 
	i++; if (i >= argc) fprintf(stderr, "ERROR! Missing filename after '-z' option.\n");
	zchaff = argv[i];
	break;
      case 'h':
	cout << doc;
	exit(0);
      }
    }
  }

  Proof P;  // minisat proof ADT
  vec<vec<Lit> > clauses; // proof  clause database
  vec<vec<Lit> > roots; // root clauses
  map<Lit,ClauseId> units; // map literal to corresponding unit clause id, if any
  int numvars = 0, numclauses = 0, conf_id;
  parsed_clauses* pclauses = new parsed_clauses(); 
  // first read CNF from original file and add to proof
  parse_DIMACS(P, roots, input, pclauses, units, numvars, numclauses);

  // then read resolvents from zchaff trace 
  vector<int> vars(numvars);   // vars[i] is pclauses idx for variable i
  parse_zChaff(zchaff, numclauses, pclauses, vars);

  // finally translate to minisat format
  Z2M translator(P,clauses,roots,units,vars,numclauses,numvars,*pclauses);
  translator.build_clauses();

  // (check) and save proof
  delete pclauses;
  Proof* current = &P;
  if (check) { // quick check
    cout << "Checking proof...\n";
    checkProof(current);
  }
  if (proof != NULL) current->save(proof); // save it
  printProofStats();
  return 0;
}

