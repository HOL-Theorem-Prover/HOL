#include <algorithm>
#include <map>
#include <set>
#include "predictor.cpp"

typedef long feature_t;
typedef long sample_t;

class NaiveBayes : public Predictor {
  public:
    NaiveBayes(LVecVec deps, LVecVec syms, LVecVec sym_ths, long sym_num);

    void learn(long from, long to);
    LDPairVec predict(const LVec& csyms, long maxth, long no_adv) const;

  private:
    double score(sample_t i, set<feature_t> symsh) const;

    void learn(const LVec& csyms, sample_t i, const LVec& cdeps);
    void add_sample_freqs(const LVec& csyms, sample_t i, long weight);

    // tfreq[t] = number of theorems having t as dependency
    vector<long> tfreq;
    // sfreq[t][f] = number of theorems having f and having t as dependency
    vector<unordered_map <feature_t, long> > sfreq;

    Tfidf tfidf;
};

NaiveBayes::NaiveBayes(LVecVec deps, LVecVec syms, LVecVec sym_ths, long sym_num)
: Predictor(deps, syms, sym_ths, sym_num), tfidf(sym_num) {
  tfreq.resize(deps.size());
  sfreq.resize(deps.size(), unordered_map <feature_t, long> (100));
}

void NaiveBayes::learn(sample_t from, sample_t to) {
  for (unsigned i = from; i < to; ++i)
    tfidf.add(syms[i]);

  for (sample_t i = from; i < to; i++)
    learn(syms[i], i, deps[i]);
}

LDPairVec NaiveBayes::predict(const LVec &csyms, sample_t maxth, long no_adv) const {
  LDPairVec ans = LDPairVec(maxth, make_pair(0, 0));

  // set of query features
  set<long> symh(csyms.begin(), csyms.end());

  for(long i = 0; i < maxth; ++i) {
    ans[i].first  = i;
    ans[i].second = score(i, symh);
  }

  sort_prediction(ans, no_adv);
  return ans;
}

double NaiveBayes::score(sample_t i, set<feature_t> symh) const {
  // number of times current theorem was used as dependency
  const long n      = tfreq[i];
  const auto sfreqh = sfreq[i];

  double s = 30 * log(n);

  /*
  for (const auto sv : sfreqh) {
    // sv.first ranges over all features of theorems depending on i
    // sv.second is the number of times sv.first appears among theorems
    // depending on i
    double sfreqv = sv.second;

    // if sv.first exists in query features
    if (symh.erase(sv.first) == 1)
      s += tfidf.get(sv.first) * log (5 * sfreqv / n);
    else
      s += tfidf.get(sv.first) * 0.2 * log (1 + (1 - sfreqv) / n);
  }

  // for all query features that did not appear in features of dependencies
  // of current theorem
  for (const auto f : symh) s -= tfidf.get(f) * 18;
  */

  return s;
}

void add_sym(unordered_map <feature_t, long> &m, feature_t sym, long w) {
  auto itr = m.find(sym);
  if (itr == m.end()) m[sym]  = w;
  else         (itr->second) += w;
}

void NaiveBayes::add_sample_freqs(const LVec& csyms, sample_t i, long w) {
  tfreq[i] += w;
  for (const auto s : csyms) add_sym(sfreq[i], s, w);
}

void NaiveBayes::learn(const LVec& csyms, sample_t i, const LVec& cdeps) {
  add_sample_freqs(csyms, i, 1000);
  for (const auto d : cdeps) add_sample_freqs(csyms, d, 1);
}

