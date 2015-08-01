#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <math.h>

using namespace std;

/* Given a file name, fills the given empty [th_no], [no_th], and sets th_num */
void read_order(const string &fname, unordered_map<string, long> &th_no,
                vector<string> &no_th) {
  ifstream ic(fname);
  string line;
  while (getline (ic, line)) {
    if (th_no.find (line) == th_no.end ()) {
      th_no[line] = no_th.size();
      no_th.push_back(line);
    } else {
      cerr << "read_order: dup: " << line; abort ();
    }
  }
}

/* Given a file name and trans, fills deps in an allocated vector of empty vectors */
void read_deps(const string &fname, unordered_map<string, long> &th_no, vector<vector<long> > &deps) {
  ifstream ic(fname);
  string line;
  while (getline (ic, line)) {
    const long colon_pos = line.find(":", 0);
    const string thn = line.substr (0, colon_pos);
    long th = th_no[thn];
    size_t start = colon_pos + 1, end = 0;
    const string delim = " ";
    if (line.size() > start)
    while (end != string::npos) {
      end = line.find(delim, start);
      auto t = line.substr(start, (end == string::npos) ? string::npos : end - start);
      start = ((end > (string::npos - delim.size())) ? string::npos : end + delim.size());
      long d=th_no[t];
      /*if (d < th)*/ deps[th].push_back(d);
      //else cerr << "future dep (ignored): " << thn << " " << t << endl;
    }
  }
}

void read_syms(const string &fname, vector<vector<long> > &syms, vector<vector<long> > &sym_ths,
               long &sym_num, const unordered_map<string,long> &th_no, unordered_map<string, long> &sym_no) {
  ifstream ic(fname);
  string line;
  while (getline (ic, line)) {
    const long colon_pos = line.find(":", 0);
    string thn = line.substr (0, colon_pos);
    auto got = th_no.find(thn);
    if (got != th_no.end () && colon_pos + 2 < line.size()) {
      if ((line.at(colon_pos+1) != '"') || (line.at(line.size () - 1) != '"'))
        {cerr << "Incorrect symbols file: no quote!" << endl; abort ();}
      long th = got->second;
      size_t start = colon_pos + 2, end = 0;
      const string delim = "\", \"";
      while (end != string::npos) {
        end = line.find(delim, start);
        auto t = line.substr(start, (end == string::npos) ? line.size() - start - 1 : end - start);
        auto got = sym_no.find (t);
        if (got == sym_no.end ()) {
          syms[th].push_back(sym_num);
          sym_no[t] = sym_num++;
          sym_ths.push_back(vector<long>(1,th));
        } else {
          syms[th].push_back(got->second);
          sym_ths[got->second].push_back(th);
        }
        start = (( end > (string::npos - delim.size()) )
                  ?  string::npos : end + delim.size());
      }
    }
  }
}

vector<long> input_sym_line(const unordered_map<string, long> &sym_no){
  string line;
  vector<long> ret;
  getline (cin, line);
  if (line.size () >= 2) {
    if ((line.at(0) != '"') || (line.at(line.size () - 1) != '"'))
      {cerr << "Incorrect input: no quote!" << endl; abort ();}
    size_t start = 1, end = 0;
    const string delim = "\", \"";
    while (end != string::npos) {
      end = line.find(delim, start);
      auto t = line.substr(start, (end == string::npos) ? line.size() - start - 1 : end - start);
      auto got = sym_no.find (t);
      if (got != sym_no.end ())
        ret.push_back(got->second);
      start = (( end > (string::npos - delim.size()) )
               ?  string::npos : end + delim.size());
    }
  }
  return ret;
}

class Tfidf {
public:
  Tfidf(const long &sym_num) : thn(0), thv(0), freq(vector<long>(sym_num, 0)), a(vector<double>(sym_num, 0)){};
  double get(long s) const {return thv - a[s];}
  double get_sum() const {
    double r = a.size() * thv;
    for (long i = 0; i < a.size(); ++i) r -= a[i];
    return r;
  }
  void add(const vector<long> &syms) {
    for(long sym = 0; sym != syms.size(); ++sym) {
      long symn = syms[sym];
      freq[symn]++; a[symn] = log(freq[symn]);
    }
    thv = log (++thn);
  }
  void add_many(const vector<vector<long> > &syms) {
    for(long i = 0; i < syms.size(); ++i)
      for(long j = 0; j < syms[i].size(); ++j)
        freq[syms[i][j]] = freq[syms[i][j]] + 1;
    for(long i = 0; i < a.size(); ++i)
      a[i] = log(freq[i]);
    thn += syms.size(); thv = log (thn);
  }
private:
  long thn;
  double thv;
  vector<long> freq;
  vector<double> a;
};

inline bool sortfun (pair<long,double> i,pair<long,double> j) {
  return (j.second < i.second);
}

inline bool sortfunl (pair<long,long> i,pair<long,long> j) {
  return (i.second < j.second);
}

void read_eval(const string &fname, unordered_map<string, long> &th_no, unordered_set<long> &eval) {
  ifstream ic(fname);
  string line;
  while (getline (ic, line)) {
    auto get = th_no.find (line);
    if (get == th_no.end ()) {
      cerr << "read_eval: none: " << line; abort ();
    } else {
      eval.insert(get->second);
    }
  }
}
