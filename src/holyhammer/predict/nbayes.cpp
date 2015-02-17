#include <algorithm>
#include <map>
#include <set>
#include "predictor.cpp"

class NaiveBayes : public Predictor {
  public:
    NaiveBayes(LVecVec deps, LVecVec syms, LVecVec sym_ths, long sym_num);

    void learn(long from, long to);
    LDPairVec predict(const LVec& csyms, long maxth, long no_adv) const;

  private:
    void learn(const LVec& csyms, long i, const LVec& cdeps);

    long afreq = 0;
    // Number of times a theorem appeared as a dependency
    vector<double> tfreq;
    // Number of times a feature was present when a theorem appeared as a dep
    vector<unordered_map <long, long> > sfreq;

    Tfidf tfidf;
};

NaiveBayes::NaiveBayes(LVecVec deps, LVecVec syms, LVecVec sym_ths, long sym_num)
: Predictor(deps, syms, sym_ths, sym_num), tfidf(sym_num) {
  tfreq.resize(deps.size());
  sfreq.resize(deps.size(), unordered_map <long,long> (100));
}

void NaiveBayes::learn(long from, long to) {
  for (unsigned i = from; i < to; ++i)
    tfidf.add(syms[i]);

  for (long i = from; i < to; i++)
    learn(syms[i], i, deps[i]);
}

LDPairVec NaiveBayes::predict(const LVec &csyms, long maxth, long no_adv) const {
  LDPairVec ans = LDPairVec(maxth, make_pair(0, 0));
  set<long> symh;

  for(long i = 0; i < maxth; ++i) {
    ans[i].first=i;
    symh.clear();
    for (const auto s : csyms) symh.insert(s);
    const long n = tfreq[i]; const auto sfreqh = sfreq[i];
    double sofar = 30 * log(n);
    for (const auto sv : sfreqh) {
      double sfreqv = sv.second;
      if (symh.erase(sv.first) == 1)
        sofar += tfidf.get(sv.first) * log (5 * sfreqv / n);
      else
        sofar += tfidf.get(sv.first) * 0.2 * log (1 + (1 - sfreqv) / n);
    }
    for (const auto s : symh) sofar -= tfidf.get(s) * 18;
    ans[i].second=sofar;
  }

  sort_prediction(ans, no_adv);
  return ans;
}

void add_sym(unordered_map <long, long> &hash, const long &sym, const long& weight) {
  auto got = hash.find(sym);
  if (got != hash.end ())
    hash[sym] += weight;
  else
    hash[sym]  = weight;
}

void NaiveBayes::learn(const LVec& csyms, long i, const LVec& cdeps) {
  afreq++;
  tfreq[i] = tfreq[i] + 1000;
  for (const auto s : csyms) add_sym(sfreq[i], s, 1000);
  for (const auto t : cdeps) {
    const long scaled_weight = 1;//pow(cdeps.size(),-0.2);
    tfreq[t] = tfreq[t] + scaled_weight;
    for (const auto s : csyms)
      add_sym(sfreq[t], s, scaled_weight);
  }
}

