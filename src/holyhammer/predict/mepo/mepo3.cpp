#include <algorithm>
#include "formatnow.cpp"

double jaccard(const vector<pair<long, double> > &syms1, const vector<pair<long, double> > &syms2,
              const Tfidf &tfidf){
  unordered_map<long, double> sym1h;
  double sig = 0, sig1 = 0, sig2 = 0;
  for (auto s = syms1.begin(); s != syms1.end(); ++s) {
    sym1h[s->first] = s->second;
    const double tw = tfidf.get(s->first);
    const double fw = s->second;
    sig1 += tw * tw * fw * fw;
  }
  for (auto s = syms2.begin(); s != syms2.end(); ++s) {
    const double tw = tfidf.get(s->first);
    const double fw = s->second;
    sig2 += tw * tw * fw * fw;
    auto got = sym1h.find(s->first);
    if (got != sym1h.end())
      sig += tw * tw * fw * got->second;
  }
  return (sig / (sig1 + sig2 + sig));
}

double cosine(const vector<pair<long, double> > &syms1, const vector<pair<long, double> > &syms2,
              const Tfidf &tfidf){
  //cerr << syms1.size() << " " << syms2.size() << "\n";
  unordered_map<long, double> sym1h;
  double sig = 0, sig1 = 0, sig2 = 0;
  for (auto s = syms1.begin(); s != syms1.end(); ++s) {
    sym1h[s->first] = s->second;
    const double tw = tfidf.get(s->first);
    const double fw = s->second;
    //cerr << "(" << s->first << "," << s->second << "," << fw << "," << tw << ")";
    sig1 += tw * tw * fw * fw;
  }
  for (auto s = syms2.begin(); s != syms2.end(); ++s) {
    const double tw = tfidf.get(s->first);
    const double fw = s->second;
    //cerr << "[" << s->first << "," << s->second << "," << fw << "," << tw << "]";
    sig2 += tw * tw * fw * fw;
    auto got = sym1h.find(s->first);
    if (got != sym1h.end())
      sig += tw * tw * fw * got->second;
  }
  return (sig * sig / (sig1 * sig2));
}

double euclid(const vector<pair<long, double> > &syms1, const vector<pair<long, double> > &syms2,
              const Tfidf &tfidf){
  unordered_map<long, double> sym1h;
  double sig = 0;
  for (auto s = syms1.begin(); s != syms1.end(); ++s)
    sym1h[s->first] = s->second;
  for (auto s = syms2.begin(); s != syms2.end(); ++s) {
    const double tw = tfidf.get(s->first);
    const double fw = s->second;
    auto got = sym1h.find(s->first);
    if (got != sym1h.end()) {
      const double diff = tw * (got->second - fw);
      sig += diff * diff;
      sym1h.erase(s->first);
    } else
      sig += tw * tw * fw * fw;
  }
  for (const auto s : sym1h) {
    const double tw = tfidf.get(s.first);
    const double fw = s.second;
    sig += tw * tw * fw * fw;
  }
  return (1 / (1 + sig));
}

static int mepo_incr = 100;

void mepo(const vector<pair<long, double> > &syms, const vector<vector<pair<long, double> > > &sym_ths,
          const vector<vector<pair<long, double> > > &allsyms, const long &maxth, double threshold,
          const Tfidf &tfidf, long more_adv, long sofar, vector<pair<long, double> > &ans){
  //cerr << "mepo: " << syms.size() << " " << sofar << "->" << more_adv << "\n";
  if (more_adv <= 0) return;
  for(long i = sofar; i < maxth; ++i)
    ans[i].second = cosine(syms, allsyms[ans[i].first], tfidf);
  partial_sort(ans.begin() + sofar, ans.begin() + sofar + more_adv, ans.begin() + maxth, sortfun);
  if (ans[0].second == 0.0) return;
  long pos = mepo_incr;
  unordered_map<long, double> nsymsh;
  for (auto s : syms) nsymsh[s.first] = s.second;
  //cerr << "thr: " << threshold << " pos: " << pos << "\n";
  pos += sofar;
  for (; sofar < pos && more_adv >= 0; sofar++) {
    more_adv--;
    const long aif = ans[sofar].first;
    const vector<pair<long, double> > thesyms = allsyms[aif];
    for (auto sw : thesyms)
      nsymsh[sw.first] = max(nsymsh[sw.first], sw.second * ans[sofar].second);
  }
  vector<pair<long, double> > nsyms;
  for (auto s : nsymsh)
    nsyms.push_back(s);
  mepo(nsyms, sym_ths, allsyms, maxth, threshold, tfidf, more_adv, sofar, ans);
}

int main(int argc, char* argv[]) {
  if (argc < 6 || argc > 7) {
    cerr << "mepo3j nei1 syms deps pred-no seq [eval]"; return 0;
  }
  char *symsf=argv[2], *depsf=argv[3], *seqf=argv[5];
  long mepo_incr=atoi(argv[1]), sym_num=0, predno=atoi(argv[4]);
  unordered_map<string, long> th_no;
  vector<string> no_th;
  read_order(seqf, th_no, no_th);// cerr << "o";
  vector<vector<long> > deps(no_th.size(), vector<long>(0));
  read_deps(depsf, th_no, deps);// cerr << "d";
  vector<vector<pair<long, double> > > syms(no_th.size(), vector<pair<long, double> >(0));
  vector<vector<pair<long, double> > > sym_ths;
  unordered_map<string, long> sym_no;
  read_syms(symsf, syms, sym_ths, sym_num, th_no, sym_no);// cerr << "s";
  Tfidf tfidf(sym_num);// cerr << "t";
  vector<pair<long, double> > ans(no_th.size(), make_pair(0, 0));
  if (argc == 7) {
    unordered_set<long> eval;
    read_eval(argv[6], th_no, eval);
    for(long i = 0; i < no_th.size(); ++i) {
      ans[i].first=i; ans[i].second=0;
    }
    for (long i = 0; i < no_th.size(); ++i) {
      if (eval.find(i) != eval.end()) {
        long no_adv = min(i, predno);
        cout << no_th[i] << ":";
        mepo(syms[i], sym_ths, syms, i, 0.6, tfidf, no_adv, 0, ans);
        for (long j = 0; j < no_adv; ++j)
          cout << no_th[ans[j].first] /*<< "(" << j << "," << ans[j].second << ")"*/ << " ";
        cout << endl;
      }
      tfidf.add(syms[i]);
    }
  } else {
    tfidf.add_many(syms);
    auto csyms = input_sym_line(sym_no);
    //cerr << syms.size();

    for(long i = 0; i < no_th.size(); ++i) {
      ans[i].first=i; ans[i].second=0;
    }

    mepo(csyms, sym_ths, syms, no_th.size(), 0.6, tfidf, predno, 0, ans);
    for (long j = 0; j < predno; ++j)
      cout << no_th[ans[j].first] /*<< "(" << ans[j].second << ")"*/ << " ";
    cout << endl;
  }
}
