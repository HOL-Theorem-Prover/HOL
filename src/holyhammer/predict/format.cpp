#ifndef FORMAT_CPP
#define FORMAT_CPP

#include <fstream>
#include <iostream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using namespace std;

typedef unordered_map<string, long> SLMap;
typedef vector<string> SVec;
typedef vector<long> LVec;
typedef vector<vector<long> > LVecVec;
typedef vector<pair<long, double> > LDPairVec;
typedef unordered_map<long, double> LDMap;

void exit_error(string message) {
  cerr << message << endl;
  exit(1);
}

/* Given a file name, fills the given empty [th_no], [no_th], and sets th_num */
void read_order(const string &fname, SLMap &th_no, SVec &no_th) {
  ifstream ic(fname);
  string line;
  while (getline (ic, line)) {
    if (th_no.find (line) == th_no.end ()) {
      th_no[line] = no_th.size();
      no_th.push_back(line);
    }
    else
      exit_error("Duplicate `" + line + 
                 "' detected upon reading file `" + fname + ".");
  }
}

/* Given a file name and trans, fills deps in an allocated vector of empty vectors */
void read_deps(const string &fname, SLMap &th_no, LVecVec &deps) {
  ifstream ic(fname);
  string line;
  while (getline (ic, line)) {
    const long colon_pos = line.find(":", 0);
    const string thn = line.substr (0, colon_pos);
    if (th_no.find (thn) == th_no.end ())
      cerr << "dep item missing in seq: " << thn << endl;
    else {
      long th = th_no[thn];
      size_t start = colon_pos + 1, end = 0;
      const string delim = " ";
      if (line.size() > start)
        while (end != string::npos) {
          end = line.find(delim, start);
          auto t = line.substr(start, (end == string::npos) ? string::npos : end - start);
          start = ((end > (string::npos - delim.size())) ? string::npos : end + delim.size());
          if (th_no.find (t) == th_no.end ())
            cerr << "dependency missing in seq: " << t << endl;
          else {
            long d=th_no[t];
            if (d < th) deps[th].push_back(d);
            else cerr << "future dep (ignored): " << thn << "(" << th << ") " << t << "(" << d << ")" << endl;
          }
        }
    }
  }
}

// parses strings of the format:
// "string1", "string2", ..., "stringn"
SVec parse_string_list(string::iterator begin, string::iterator end) {
  SVec result;

  while (true) {
    if (begin == end || *begin != '"')
      exit_error("Feature start with double quote expected!");

    const auto closing_quote = find(begin + 1, end, '"');
    if (closing_quote == end)
      exit_error("Features stop with double quote expected!");

    result.push_back(string(begin + 1, closing_quote));

    const auto comma = closing_quote + 1;
    if (comma == end)
      break;
    else {
      const auto space = comma + 1;
      if (space == end)
        exit_error("Space expected after comma!");
      else if (*comma != ',' || *space != ' ')
        exit_error("Comma and space expected after feature!");

      begin = space + 1;
    }
  }

  return result;
}

// parses strings of the format:
// thmid:"feature1", "feature2", ..., "featuren"
void read_syms(const string &fname, LVecVec &syms, LVecVec &sym_ths,
               long &sym_num, const SLMap &th_no,
               SLMap &sym_no, SVec& no_sym) {
  ifstream ic(fname);
  string line;
  while (getline(ic, line)) {
    const auto colon = find(line.begin(), line.end(), ':');
    if (colon == line.end())
      exit_error("Expected colon in line `" + line + "'!");

    string th_str(line.begin(), colon);
    auto th_got = th_no.find(th_str);
    if (th_got == th_no.end())
      exit_error("Theorem `" + th_str + "' not found!");
    long th = th_got->second;

    SVec features = parse_string_list(colon + 1, line.end());
    for (const auto& f : features) {
      auto ftr_got = sym_no.find(f);
      if (ftr_got == sym_no.end()) {
        syms[th].push_back(sym_num);
        sym_ths.push_back(vector<long>(1,th));

        // register new feature
        sym_no[f] = sym_num++;
        no_sym.push_back(f);
      }
      else {
        syms[th].push_back(ftr_got->second);
        sym_ths[ftr_got->second].push_back(th);
      }
    }
  }
}

LVec parse_feature_list(string::iterator begin, string::iterator end,
  const SLMap& ftr_no) {
  LVec result;
  for (const auto& f : parse_string_list(begin, end)) {
    auto got = ftr_no.find(f);
    if (got != ftr_no.end())
      result.push_back(got->second);
  }

  return result;
}

void read_eval(const string &fname, unordered_map<string, long> &th_no,
               unordered_set<long> &eval) {
  ifstream ic(fname);
  string line;
  while (getline(ic, line)) {
    auto get = th_no.find (line);
    if (get == th_no.end())
      exit_error("Could not find theorem `" + line +
                 "' in file `" + fname + "'.");
    else
      eval.insert(get->second);
  }
}

#endif

