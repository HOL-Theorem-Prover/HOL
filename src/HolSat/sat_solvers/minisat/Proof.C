/*****************************************************************************************[Proof.C]
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

#include "Proof.h"
#include "Sort.h"
#include <iostream>

//=================================================================================================
// Temporary files handling:


class TempFiles {
    vec<cchar*> files;      // For clean-up purposed on abnormal exit.

public:
   ~TempFiles()
    {
        for (int i = 0; i < files.size(); i++)
            remove(files[i]);
            //printf("Didn't delete:\n  %s\n", files[i]);
    }

    // Returns a read-only string with the filename of the temporary file. 
    // The pointer can be used to 
    // remove the file (which is otherwise done automatically upon program exit).
    //
    char* open(File& fp)
    {
        char*   name;
        for(;;){
            name = tempnam(NULL, NULL);
            assert(name != NULL);
            fp.open(name, "wx+");
            if (fp.null())
                xfree(name);
            else{
                files.push(name);
                return name;
            }
        }
    }
};
static TempFiles temp_files;       // (should be singleton)


//=================================================================================================
// Proof logging:

Proof::Proof()
{
    fp_name    = temp_files.open(fp);
    id_counter = 1; //HA: to save sign info on-the-fly, unit_id uses -ve clause id's to indicate
                    //    that the clause literal is negated, so can't use 0
    root_counter = 1;
    trav       = NULL;
    c2fp.push(0); // dummy argument (placeholder for clause ID 0 which does not exist)
}

Proof::Proof(ProofTraverser& t)
{
    id_counter = 1;
    root_counter = 1;
    trav       = &t;
    c2fp.push(0);
}

ClauseId Proof::addRoot(vec<Lit>& cl, ClauseId orig_root_id)
{
    cl.copyTo(clause);

    sortUnique(clause);

    if (trav != NULL) 
        trav->root(clause);

    if (!fp.null()){ 
            
	fp.setMode(READ);
	c2fp.push(fp.tell());
	fp.seek(0, SEEK_END);
	fp.setMode(WRITE);      

        putUInt(fp, -1 == orig_root_id ? root_counter << 1 : orig_root_id << 1);
        putUInt(fp, index(clause[0]));
        for (int i = 1; i < clause.size(); i++)
            putUInt(fp, index(clause[i]) - index(clause[i-1]));
        putUInt(fp, 0);     // (0 is safe terminator since we removed duplicates)
    }
    root_counter++;
    return id_counter++;
}

void Proof::beginChain(ClauseId start)
{
    assert(start != ClauseId_NULL);
    chain_id .clear();
    chain_var.clear();
    chain_id.push(abs(start)); //HA: the abs
    //std::cout << "B " << abs(start);
}

void Proof::resolve(ClauseId next, Var x)
{
    assert(next != ClauseId_NULL);
    chain_id .push(abs(next)); //HA: abs
    if (next>=0) chain_var.push(x << 1);
    else chain_var.push((x << 1) | 1); // HA: adding sign info to pivots
}

void Proof::resolve(ClauseId next, Lit p)
{
    assert(next != ClauseId_NULL);
    chain_id .push(abs(next)); //HA: abs
    chain_var.push(index(p));
    //std::cout << " (" << index(p) << "," << next << ")";
}

ClauseId Proof::endChain()
{
    assert(chain_id.size() == chain_var.size() + 1);
    //std::cout << std::endl;
    if (chain_id.size() == 1)
        return chain_id[0];
    else{
        if (trav != NULL)
            trav->chain(chain_id, chain_var);
        if (!fp.null()){

	  fp.setMode(READ);
	  c2fp.push(fp.tell()); 
	  fp.seek(0, SEEK_END);
	  fp.setMode(WRITE);

	  putUInt(fp, ((id_counter - chain_id[0]) << 1) | 1);
	                                       
            for (int i = 0; i < chain_var.size(); i++)
	      putUInt(fp, chain_var[i] + 1),
                putUInt(fp, id_counter - chain_id[i+1]);
            putUInt(fp, 0);
        }

        return id_counter++;
    }
}

void Proof::deleted(ClauseId gone)
{
    if (trav != NULL)
        trav->deleted(abs(gone));
    if (!fp.null()){
        putUInt(fp, ((id_counter - (abs(gone))) << 1) | 1);
        putUInt(fp, 0);
    }
}


//=================================================================================================
// Read-back methods:

//HA: fill up "clause" as a root clause
#ifdef DEBUG
ClauseId Proof::parseRoot(vec<Lit>& clause, File& fp, uint64 tmp, std::ofstream* fout) {
#else 
ClauseId Proof::parseRoot(vec<Lit>& clause, File& fp, uint64 tmp) {
#endif

  int idx,idx0;
{
#ifdef DEBUG
  if (NULL != fout) (*fout) << "r ";
#endif
}
  clause.clear();
  idx0 = tmp >> 1; // the root_counter value
  idx = getUInt(fp);
{
#ifdef DEBUG
  if (NULL != fout) (*fout) << idx;
#endif
}
  clause.push(toLit(idx));
  for(;;){
    tmp = getUInt(fp);
    if (tmp == 0) break;
    idx += tmp;
{
#ifdef DEBUG
    if (NULL != fout) (*fout) << " " << idx;
#endif
}
    clause.push(toLit(idx));
  }
{
#ifdef DEBUG
  if (NULL != fout) (*fout) << "\n";
#endif
}
  return idx0; 
}

//HA: fill up chain_id and chain_var
#ifdef DEBUG
void Proof::parseChain(vec<ClauseId>&   chain_id, vec<Var>&  chain_var, 
		       File& fp, uint64 tmp, ClauseId id, std::ofstream* fout) {
#else
void Proof::parseChain(vec<ClauseId>&   chain_id, vec<Var>&  chain_var, 
		       File& fp, uint64 tmp, ClauseId id) {
#endif

  chain_id .clear();
  chain_var.clear();
  chain_id.push(id - (tmp >> 1));
{
#ifdef DEBUG
  if (NULL != fout) (*fout) << "B " << (id - (tmp >> 1)) << " ";
#endif
}

  for(;;){
    tmp = getUInt(fp);
    if (tmp == 0) break;
    chain_var.push(tmp - 1);
{
#ifdef DEBUG
    if (NULL != fout) (*fout) << " " << (tmp-1);
#endif
}

    tmp = getUInt(fp);
    chain_id.push(id - tmp);
{
#ifdef DEBUG
    if (NULL != fout) (*fout) << " " << (id-tmp) << "  ";
#endif
}
  }
}

void Proof::compress(Proof& dst, ClauseId goal)
{
    assert(!fp.null());
    fp.setMode(READ);
    vec<ClauseId> dfs_stack; // stack for simulating "backwards" DFS
    vec<vec<ClauseId> > chain_id_stack;
    vec<vec<Var> > chain_var_stack;
    vec<ClauseId> c2c(goal+2,-1); // c2c[old_id] is new id in compressed proof of clause old_id

#ifdef DEBUG
    std::ofstream fout ("filter.fdb");     // Output for debugging
#endif

    dfs_stack.push(goal);
    ClauseId id = dfs_stack.last();
    while (dfs_stack.size()>0) {
      id = dfs_stack.last();
      switch  (c2c[id]) {
      case -2 : // a chain that has been visited before. write it out now
	{
	  //int64 pos = c2fp[id];
	  //fp.seek(pos);
	  //uint64 tmp = getUInt(fp);
	  //parseChain(chain_id,chain_var,fp,tmp,id); 
	  chain_id_stack.last().copyTo(chain_id); chain_id_stack.pop();
	  chain_var_stack.last().copyTo(chain_var); chain_var_stack.pop();
	  int sz = chain_id.size();
	  for (int i=0; i<sz; i++)  // redirect chain_id[i]'s to new id's
	    chain_id[i]=c2c[chain_id[i]];
          dst.beginChain(chain_id[0]);
          for (int i=1;i<sz;i++) 
            dst.resolve(chain_var[i-1] & 1 ? -1*chain_id[i] : chain_id[i],chain_var[i-1] >> 1);	  
          c2c[id] = dst.endChain();
	  dfs_stack.pop();
{        	
#ifdef DEBUG
  fout << c2c[id] << " B [" << id << "] : ";
  for (int i=0;i<chain_var.size();i++)      
    fout << " " << chain_var[i] << " ";
  fout << "::";	
  for (int i=0; i<sz; i++)  
    fout << " " << chain_id[i] << " ";
  fout << "\n";
#endif
}
	  break;
	}
      case -1 : // this root/chain has not been visited before
	{
	  int64 pos = c2fp[id];
	  fp.seek(pos);
	  uint64 tmp = getUInt(fp);
	  if ((tmp & 1) == 0) { // if root, just write it out
	    ClauseId orig_root_id = parseRoot(clause,fp,tmp);
	    c2c[id] = dst.addRoot(clause,orig_root_id); 

{
#ifdef DEBUG
  fout << c2c[id] << " R [" << ((tmp>>1)-1) << "]\n"; //debug
#endif
}
            dfs_stack.pop();
	  } else { // if chain, process antecedent clauses first   
	    parseChain(chain_id,chain_var,fp,tmp,id); 
	    chain_id_stack.push(); chain_id.copyTo(chain_id_stack.last());
	    chain_var_stack.push(); chain_var.copyTo(chain_var_stack.last());
	    int sz = chain_id.size();
	    for (int i=0; i<sz; i++) 
	      dfs_stack.push(chain_id[i]);	  
	    c2c[id] = -2; // means a chain that has been visited but not written out yet           
	  }
	  break;
	}
      default: // this one's already been processed. 
        dfs_stack.pop(); 
     }
   }
{
#ifdef DEBUG
 fout.close();
#endif
}
}


bool Proof::save(cchar* filename)
{
    assert(!fp.null());

    // Switch to read mode:
    fp.setMode(READ);
    fp.seek(0);

    // Copy file:
    File    out(filename, "wox");

    if (out.null())
        return false;

    while (!fp.eof()) {
      out.putChar(fp.getChar());
    }

    // Restore write (proof-logging) mode:
    fp.seek(0, SEEK_END);
    fp.setMode(WRITE);
    return true;
}

void Proof::traverse(ProofTraverser& trav, int& res_count, ClauseId goal)
{
    assert(!fp.null());

    // Switch to read mode:
    fp.setMode(READ);
    fp.seek(0);
    
    // Traverse proof:
    if (goal == ClauseId_NULL) 
      goal = last(); 

#ifdef DEBUG
    std::ofstream fout ("proof.trv");
    fout << "G " << goal << "\n";
#endif

    uint64  tmp;

    for(ClauseId id = 1; id <= goal; id++){
      tmp = getUInt(fp);
      if ((tmp & 1) == 0){
	// Root clause:
#ifdef DEBUG
	parseRoot(clause,fp,tmp,&fout);
#else 
	parseRoot(clause,fp,tmp);
#endif
	trav.root(clause);
      } else {
	// Derivation or Deletion:
#ifdef DEBUG
	parseChain(chain_id,chain_var,fp,tmp,id,&fout);
#else 
	parseChain(chain_id,chain_var,fp,tmp,id);
#endif
	res_count+=chain_var.size();
	if (chain_var.size() == 0)
	  id--,   // (no new clause introduced)
	    trav.deleted(chain_id[0]-1); //HA: -1 to compensate for id_counter base 1
	else
	  trav.chain(chain_id, chain_var);
      }
    }
    trav.done();
#ifdef DEBUG
    fout.close();
#endif
    // Restore write (proof-logging) mode:
    fp.seek(0, SEEK_END);
    fp.setMode(WRITE);
}
