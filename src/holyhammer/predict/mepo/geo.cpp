#include <algorithm>
#include "format.cpp"

void geo(const vector<long> &syms, const vector<vector<long> > &sym_ths,
         const vector<vector<long> > &deps, const long &maxth,
         const long recurse, const double factor, const Tfidf &tfidf,
         const long no_adv, vector<pair<long, double> > &ans){
  for(long i = 0; i < maxth; ++i) {
    ans[i].first=i; ans[i].second=0;
  }
  for(long sym = 0; sym != syms.size(); ++sym) {
    long symn = syms[sym];
    vector<long> ths = sym_ths[symn];
    double wght = tfidf.get(symn);
    for(auto th = ths.begin(); th != ths.end(); ++th) {
      if (*th < maxth) ans[*th].second += wght * wght;
    }
  }
  if (recurse) {
    for(long i = maxth - 1; i >= 0; --i) {
      double v = factor * ans[i].second;
      if (v > 0) {
        vector<long> ds = deps[i];
        for(auto d = ds.begin(); d != ds.end(); ++d)
          ans[*d].second = max(ans[*d].second, v);
      }
    }
  } else {
    for(int i = 0; i < maxth; ++i) {
      double v = factor * ans[i].second;
      if (v > 0) {
        vector<long> ds = deps[i];
        for(auto d = ds.begin(); d != ds.end(); ++d)
          ans[*d].second = max(ans[*d].second, v);
      }
    }
  }
  partial_sort(ans.begin(), ans.begin() + no_adv, ans.begin() + maxth, sortfun);
}

int main(int argc, char* argv[]) {
  if (argc < 7 || argc > 8) {
    cerr << "geo recurse factor syms deps pred-no seq [eval]"; return 0;
  }
  char *symsf=argv[3], *depsf=argv[4], *seqf=argv[6];
  long recurse=atoi(argv[1]), sym_num=0, predno=atoi(argv[5]);
  double factor=atof(argv[2]);
  unordered_map<string, long> th_no;
  vector<string> no_th;
  read_order(seqf, th_no, no_th);// cerr << "o";
  vector<vector<long> > deps(no_th.size(), vector<long>(0));
  read_deps(depsf, th_no, deps);// cerr << "d";
  vector<vector<long> > syms(no_th.size(), vector<long>(0));
  vector<vector<long> > sym_ths;
  unordered_map<string, long> sym_no;
  read_syms(symsf, syms, sym_ths, sym_num, th_no, sym_no);// cerr << "s";
  Tfidf tfidf(sym_num);// cerr << "t";
  vector<pair<long, double> > ans(no_th.size(), make_pair(0, 0));
  if (argc == 8) {
    unordered_set<long> eval;
    read_eval(argv[7], th_no, eval); // cerr << "e";
    for (long i = 0; i < no_th.size(); ++i) {
      if (eval.find(i) != eval.end()) {
        long no_adv = min(i, predno);
        cout << no_th[i] << ":";
        geo(syms[i], sym_ths, deps, i, recurse, factor, tfidf, no_adv, ans);
        for (long j = 0; j < no_adv; ++j)
          cout << no_th[ans[j].first] /*<< "(" << ans[j].second << ")"*/ << " ";
        cout << endl;
      }
      tfidf.add(syms[i]);
    }
  } else {
    tfidf.add_many(syms);
    auto syms = input_sym_line(sym_no);
    geo(syms, sym_ths, deps, no_th.size(), recurse, factor, tfidf, predno, ans);
    for (long j = 0; j < predno; ++j)
      cout << no_th[ans[j].first] /*<< "(" << ans[j].second << ")"*/ << " ";
    cout << endl;
  }
}
