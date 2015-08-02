#ifndef PREDICTOR_CPP
#define PREDICTOR_CPP

#include <cmath>
#include "format.cpp"
#include "tfidf.cpp"

class Predictor {
  public:
    Predictor(LVecVec deps, LVecVec syms, LVecVec sym_ths, long sym_num);
    virtual ~Predictor() {}

    virtual void learn(long from, long to) = 0;  // learn [from, ..., to)
    void learn_all();

    LDPairVec predict(long i, long maxth, long no_adv);
    virtual LDPairVec predict(const LVec& csyms, long maxth, long no_adv) const = 0;

    void set_tables(SVec no_th, SVec no_sym, SLMap th_no, SLMap sym_no);

    virtual void import_data(string location) {}
    virtual void export_data(string location) const {}

  protected:
    LVecVec deps,         // dependencies of each theorem
            syms,         // syms[t] holds the symbols of a theorem t
            sym_ths;      // sym_ths[s] holds the theorems which contain s

    SVec no_th,
         no_sym;
    SLMap  th_no,
          sym_no;

  private:
    void print_answer(long no_adv);
};

Predictor::Predictor(LVecVec deps, LVecVec syms, LVecVec sym_ths, long sym_num)
  : deps(deps), syms(syms), sym_ths(sym_ths) {}

void Predictor::learn_all() {
  learn(0, syms.size() - 1);
}

LDPairVec Predictor::predict(long i, long maxth, long n_predictions) {
  return predict(syms[i], maxth, n_predictions);
}

void Predictor::set_tables(SVec no_th, SVec no_sym, SLMap th_no, SLMap sym_no) {
  this->no_th  = no_th;
  this->no_sym = no_sym;
  this->th_no  = th_no;
  this->sym_no = sym_no;
}

inline bool sortfun (pair<long,double> i, pair<long,double> j) {
  return (j.second < i.second);
}

// sort the theorem-probability table such that the first n_predictions
// elements of it contain the best predictions
void sort_prediction(LDPairVec& prediction, long n_predictions) {
  partial_sort(prediction.begin(), prediction.begin() + n_predictions,
    prediction.end(), sortfun);
}

#endif
