/***********************************************************************************[SolverTypes.h]
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


#ifndef SolverTypes_h
#define SolverTypes_h

#ifndef Global_h
#include "Global.h"
#endif


//=================================================================================================
// Variables, literals, clause IDs:


// NOTE! Variables are just integers. No abstraction here. They should be chosen from 0..N,
// so that they can be used as array indices.

typedef int Var;
#define var_Undef (-1)


class Lit {
    int     x;
public:
    Lit() : x(2*var_Undef) {}   // (lit_Undef)
    explicit Lit(Var var, bool sign = false) : x((var+var) + (int)sign) { }//HA: +ve lit is 2v, -ve lit is 2v+1
    friend Lit operator ~ (Lit p) { Lit q; q.x = p.x ^ 1; return q; }//HA: negate lit: flip the lsb

    friend bool sign  (Lit p) { return p.x & 1; } //HA:is the lsb 1? true if lit is -ve i.e. is signed
    friend int  var   (Lit p) { return p.x >> 1; } //HA:drop sign info and div by 2 i.e. get corresponding var 
    friend int  index (Lit p) { return p.x; } // A "toInt" method that guarantees small, 
                                              // positive integers suitable for array indexing.
    friend Lit  toLit (int i) { Lit p; p.x = i; return p; }  // Inverse of 'index()'.
    friend Lit  unsign(Lit p) { Lit q; q.x = p.x & ~1; return q; }
    friend Lit  id    (Lit p, bool sgn) { Lit q; q.x = p.x ^ (int)sgn; return q; }

    friend bool operator == (Lit p, Lit q) { return index(p) == index(q); }
    friend bool operator <  (Lit p, Lit q) { return index(p)  < index(q); }  // '<' guarantees that p, 
                                                                             // ~p are adjacent in the ordering.
};

const Lit lit_Undef(var_Undef, false);  // }- Useful special constants.
const Lit lit_Error(var_Undef, true );  // }


//=================================================================================================
// Clause -- a simple class for representing a clause:


typedef int ClauseId;     // (might have to use uint64 one day...)
const   int ClauseId_NULL = INT_MIN;

//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

class Clause {
    uint    size_learnt;
    Lit     data[0];
public:
    // NOTE: This constructor cannot be used directly (doesn't allocate enough memory).
    Clause(bool learnt, const vec<Lit>& ps, ClauseId id_ = ClauseId_NULL) {
        size_learnt = (ps.size() << 1) | (int)learnt;
        for (int i = 0; i < ps.size(); i++) data[i] = ps[i];
        if (learnt) activity() = 0;
        if (id_ != ClauseId_NULL) id() = id_; }

    // -- use this function instead:
    friend Clause* Clause_new(bool learnt, const vec<Lit>& ps, ClauseId id = ClauseId_NULL) {
        assert(sizeof(Lit)      == sizeof(uint));
        assert(sizeof(float)    == sizeof(uint));
        assert(sizeof(ClauseId) == sizeof(uint));
        void*   mem = xmalloc<char>(sizeof(Clause) + sizeof(uint)*(ps.size() + (int)learnt + (int)(id != ClauseId_NULL)));
        return new (mem) Clause(learnt, ps, id); }

    int       size        ()      const { return size_learnt >> 1; }
    bool      learnt      ()      const { return size_learnt & 1; }
    Lit       operator [] (int i) const { return data[i]; }
    Lit&      operator [] (int i)       { return data[i]; }
    float&    activity    ()      const { return *((float*)&data[size()]); }
    ClauseId& id          ()      const { return *((ClauseId*)&data[size() + (int)learnt()]); }
};


//=================================================================================================
#endif
