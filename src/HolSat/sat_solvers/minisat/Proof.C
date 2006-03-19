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
#include <fstream>

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

    // Returns a read-only string with the filename of the temporary file. The pointer can be used to 
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
//HA: if proof loggin is on, Solver calls these methods, which record a trace that can then be read
//    back by proof traverser, say for checking the proof
//    the recording is done straight to disk using random access, to keep ram free for Solver itself
//HA: note these are not only called by Solver.newClause but from elsewhere as well, so my understanding
//     of this is incomplete

Proof::Proof()
{
    fp_name    = temp_files.open(fp);
    id_counter = 0;
    trav       = NULL;
}


Proof::Proof(ProofTraverser& t)
{
    id_counter = 0;
    trav       = &t;
}

//HA: this is called whenever Solver.newClause discovers a conflict clause
//HA: it is always called as an argument to Proof::beginChain
//HA: hence it's return value forms the "start" argument to beginChain 
ClauseId Proof::addRoot(const vec<Lit>& cl)
{
    cl.copyTo(clause);
    //sortUnique(clause);//HA:this is required because of the root clause is stored as +ve difference of literals
    //HA: but I've commented it out because right now it is only called from Solver::newClause where sortUnique happens 
    //already

    if (trav != NULL) //HA: if there is a traverser then call the appropriate traversal function
        trav->root(clause);
    if (!fp.null()){ //HA: if we are recording then write out this clause to fp
        putUInt(fp, index(clause[0]) << 1);
        for (int i = 1; i < clause.size(); i++)
	  //HA: not sure why clause is saved in this fashion (perhaps to keep the numbers small)
          //HA:  it is read back in a consistent manner (see traverse) so doesn't really matter I guess
            putUInt(fp, index(clause[i]) - index(clause[i-1]));
        putUInt(fp, 0);     // (0 is safe terminator since we removed duplicates)
    }

    return id_counter++;
}

//HA: called by solver to signal the start of a conflict resolution chain
//HA:  is this the chain that gets traversed when checking the proof: yes
//HA:   because if Solver.newClause finds unsat, it calls Proof::endChain, which writes out the current conflict
//HA:   resolution chain
//HA: so beginChain clears chains corresponding to any previous conflicts that got fixed
//HA: However, earlier chains that got written out are not cleared, 
//HA: so really one can have several chains in the proof trace
void Proof::beginChain(ClauseId start)
{
    assert(start != ClauseId_NULL);
    chain_id .clear();
    chain_var.clear();
    chain_id.push(start);
}

//HA: when solver finds a conflict clause, this function is called for all false lits in that clause, since any
//HA: one of them could be contributing to the conflict. 
//HA: first arg is the clause ID of the unit literal var or ~var, second arg is the var of that lit
//HA: so first arg is the antecedent clause for var x
//HA: but how does Solver.newClause know that var x must have an antecedent??
void Proof::resolve(ClauseId next, Var x)
{
    assert(next != ClauseId_NULL);
    chain_id .push(next);
    chain_var.push(x);
}

//HA: writes out current conflict resolution chain
//HA: this is enough to find unsat proof because if unsat was discovered, then the discovery must have led from the
//HA:  the last conflict clause found, which is when this chain was begun.
ClauseId Proof::endChain()
{
    assert(chain_id.size() == chain_var.size() + 1);
    if (chain_id.size() == 1)
        return chain_id[0];
    else{
        if (trav != NULL)
            trav->chain(chain_id, chain_var);
        if (!fp.null()){
	  putUInt(fp, ((id_counter - chain_id[0]) << 1) | 1);//HA:shift up and force last bit to 1
	                                                     //HA: this way we can distinguish it from root clause
            for (int i = 0; i < chain_var.size(); i++)
	      putUInt(fp, chain_var[i] + 1),//HA:write out var
                putUInt(fp, id_counter - chain_id[i+1]);//HA:write out clause ID
            putUInt(fp, 0);
        }

        return id_counter++;
    }
}


void Proof::deleted(ClauseId gone)
{
    if (trav != NULL)
        trav->deleted(gone);
    if (!fp.null()){
        putUInt(fp, ((id_counter - gone) << 1) | 1);
        putUInt(fp, 0);
    }
}


//=================================================================================================
// Read-back methods:


void Proof::compress(Proof& dst, ClauseId goal)
{
    assert(!fp.null());
    assert(false);  // Not yet!    
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

    //HA1:putUInt(out,last()); //HA: to make my life easier when parsing into HOL

    while (!fp.eof()) {
      int c = fp.getChar();
      out.putChar(c);
    }

    // Restore write (proof-logging) mode:
    fp.seek(0, SEEK_END);
    fp.setMode(WRITE);
    return true;
}

//HA: if proof logging was on, then Solver will have recorded the required info into fp
//HA: this takes that info and traverses the resolvent graph, looking for the empty clause
void Proof::traverse(ProofTraverser& trav, char* fname,  ClauseId goal)
{
    assert(!fp.null());

    // Switch to read mode:
    fp.setMode(READ);
    fp.seek(0);
    int l = strlen(fname);
    fname[l-1] = 'v';    fname[l-2] = 'r';    fname[l-3] = 't';
    std::ofstream fout (fname);

    // Traverse proof:
    if (goal == ClauseId_NULL) //HA: this is always true for the moment, since Main.checkProof gives no second arg
      goal = last(); //HA: so this get the clause ID of the last clause that the solver considered in conflict analysis
    fout << "G " << goal << "\n";
    uint64  tmp;
    int     idx;
    for(ClauseId id = 0; id <= goal; id++){
        tmp = getUInt(fp);
        if ((tmp & 1) == 0){
	    // Root clause:
	  fout << "r ";
            clause.clear();
            idx = tmp >> 1;
	    fout << idx;
            clause.push(toLit(idx));
            for(;;){
                tmp = getUInt(fp);
                if (tmp == 0) break;
                idx += tmp;
		fout << " " << idx;
                clause.push(toLit(idx));
            }
	    fout << " ~3\n";
            trav.root(clause);

        }else{
            // Derivation or Deletion:
            chain_id .clear();
            chain_var.clear();
            chain_id.push(id - (tmp >> 1));
	    fout << "B " << (id - (tmp >> 1)) << " ";
	  
            for(;;){
                tmp = getUInt(fp);
                if (tmp == 0) break;
                chain_var.push(tmp - 1);
		fout << " " << (tmp-1);
                tmp = getUInt(fp);
                chain_id.push(id - tmp);
		fout << " " << (id-tmp) << "  ";
            }
	    if (chain_var.size() == 0) fout << " ~2 ~3\n"; else fout << " ~1 ~3\n";

            if (chain_var.size() == 0)
                id--,   // (no new clause introduced)
                trav.deleted(chain_id[0]);
            else
                trav.chain(chain_id, chain_var);
        }
    }
    trav.done();
    fout.close();
    // Restore write (proof-logging) mode:
    fp.seek(0, SEEK_END);
    fp.setMode(WRITE);
}
