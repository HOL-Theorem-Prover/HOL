#include <algorithm>
#include "predictor.cpp"

class kNN : public Predictor {
  public:
    kNN(LVecVec deps, LVecVec syms, LVecVec sym_ths, long sym_num);

    void learn(long from, long to);

  protected:
    LDPairVec predict(const LVec& csyms, long maxth, long no_adv) const;

  private:
    Tfidf tfidf;
};

kNN::kNN(LVecVec deps, LVecVec syms, LVecVec sym_ths, long sym_num)
: Predictor(deps, syms, sym_ths, sym_num), tfidf(sym_num) {
}

void kNN::learn(long from, long to) {
  for (unsigned i = from; i < to; ++i)
    tfidf.add(syms[i]);
}

inline double age(long k) {
  return 500000000 - 100 * k;
}

LDPairVec kNN::predict(const LVec& csyms, long maxth, long no_adv) const {
  LDPairVec ans = LDPairVec(maxth, make_pair(0, 0));

  // initialise theorem importance matrix
  for (long i = 0; i < maxth; ++i) {
    ans[i].first=i; ans[i].second=0;
  }

  // for each symbol, increase the importance of the theorems which contain
  // the symbol by a given symbol weight
  for (const auto& sym : csyms) {
    vector<long> ths = sym_ths[sym];
    double weight = tfidf.get(sym);
    for (const auto& th : ths) {
      if (th < maxth) ans[th].second += pow(weight, 6);
    }
  }

  LDPairVec neighbours(maxth);
  partial_sort_copy(ans.begin(), ans.begin() + maxth, neighbours.begin(), neighbours.end(), sortfun);
  for (long i = 0; i < maxth; ++i) ans[i].second=0;


  // In typical k-NN implementation the number 'k' is fixed. Unfortunately for
  // premise selection, using a wrong number may have quite bad implications,
  // namely the neighbours may all be very similar and have very similiar dependencies.
  // This may mean that we will not have enough non-zero entries to fill no-adv predictions.
  // This is why we use an adaptive 'k'. We count how many premises we recommended,
  // and we continue until this number is enough.
  // Since we want to sort the list of recommended answers only once, we want to make
  // sure that items recommended by a certain 'k' are before those coming for the increased
  // k. In order to do this, we use an "age" that is added to non-zero predictions
  // and decreases when k increases.

  long no_recommends = 0;
  for (long k = 0; k < maxth && no_recommends < no_adv; ++k) {
    long nn = neighbours[k].first;
    double o = neighbours[k].second; // distance, we do not use sqrt
    if (ans[nn].second <= 0) {
      no_recommends++;
      ans[nn].second = age(k) + o;
    }
    else
      ans[nn].second += o;

    // dependencies of the neighbor also gain some relevance, depending on the
    // number of dependencies of the current theorem
    LVec ds = deps[nn];
    double ol = 2.7 * o / ds.size();
    for (const auto& d : ds) {
      if (d < maxth) { // in case of future dependencies, do not predict them
        if (ans[d].second <= 0) {
          no_recommends++;
          ans[d].second = age(k) + ol;
        }
        else
          ans[d].second += ol;
      }
    }
  }

  sort_prediction(ans, no_adv);
  return ans;
}
