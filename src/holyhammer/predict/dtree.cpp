#ifndef DTREE_CPP
#define DTREE_CPP

#include <cassert>
#include <regex>

typedef unordered_map<long, unsigned> LUMap;

class DecisionTree {
  public:
    // trees which have (left) and which do not have (right) feature
    DecisionTree *left = NULL, *right = NULL;
    long feature = -1;
    LVec labels;
    LUMap features_freq;
    long n_samples = 0;

    DecisionTree(LVec labels = LVec()) : labels(labels) {}
    DecisionTree(DecisionTree *left, DecisionTree *right, long feature)
      : left(left), right(right), feature(feature) {}
    DecisionTree(string filename, const SLMap& th_no, const SLMap& sym_no);

    ~DecisionTree() { delete left; delete right; }

    bool is_leaf() const { return (left == NULL) || (right == NULL); }
    long height() const {
      if (is_leaf()) return 1;
      else           return 1 + max(left->height(), right->height());
    }

    void add_labels_recursively(LVec& result) const;

    void query(const LVec& features, LDMap& result, double weight) const;
    void write_to_file(string filename,
      const SVec& no_th, const SVec& no_sym) const;

  private:
    string dot(string pos, const SVec& no_th, const SVec& no_sym) const;

    const double punish_weight = 0.05;
    const double min_weight = punish_weight*punish_weight;
};

void DecisionTree::add_labels_recursively(LVec& result) const {
  if (is_leaf())
    result.insert(result.end(), labels.begin(), labels.end());
  else {
    left ->add_labels_recursively(result);
    right->add_labels_recursively(result);
  }
}

void DecisionTree::query(const LVec& features, LDMap& result, double weight = 1.0)
  const {
  if (weight < min_weight)
    return;

  if (is_leaf())
    for (const auto& l : labels)
      result[l] += weight;
  else {
    double lweight = weight,
           rweight = weight;

    LVec::const_iterator fitr = find(features.begin(), features.end(), feature);
    if (fitr == features.end())
      lweight *= punish_weight;
    else
      rweight *= punish_weight;

     left->query(features, result, lweight);
    right->query(features, result, rweight);
  }
}

DecisionTree::DecisionTree(string filename,
  const SLMap& th_no, const SLMap& sym_no) : DecisionTree() {

  ifstream f(filename);

  if (f.is_open()) {
    string line;

    while (getline(f, line)) {
      if (line.find("->") != string::npos ||
          line == "digraph tree {" ||
          line == "  node [shape=box]" ||
          line == "}")
        continue;
      else {
        DecisionTree *pos = this;
        bool is_feature = true;

        auto p = find_if_not(line.begin(), line.end(),
          [](char c) { return c == ' '; } );
        if (p == line.end() || *p != 't')
          exit_error("Tree position expected!");
        p++;

        while (p != line.end()) {
          if (*p == ' ')
            break;

          switch (*p) {
            case 'l':
              if (pos->left == NULL) pos->left = new DecisionTree;
              pos = pos->left;
              break;
            case 'r':
              if (pos->right == NULL) pos->right = new DecisionTree;
              pos = pos->right;
              break;
            default:
              if (isdigit(*p))
                is_feature = false;
              else
                exit_error("Unknown character in tree position found.");
          }

          p++;
        }
        if (*p != ' ')
          exit_error("Content expected after tree position.");

        auto opening_quote = find(p + 1, line.end(), '"');
        if (opening_quote == line.end())
          exit_error("Opening quote not found.");
        auto closing_quote = find(opening_quote + 1, line.end(), '"');
        if (closing_quote == line.end())
          exit_error("Closing quote not found.");

        string name_str(opening_quote + 1, closing_quote);

        if (is_feature) {
          auto sym = sym_no.find(name_str);
          if (sym == sym_no.end())
            exit_error("Could not find feature `" + name_str + "'");
          else
            pos->feature = sym->second;
        }
        else {
          auto th = th_no.find(name_str);
          if (th == th_no.end())
            exit_error("Could not find label `" + name_str + "'");
          else
            pos->labels.push_back(th->second);
        }
      }
    }
    f.close();
  }
  else
    exit_error("Could not read file `" + filename + "'.");
}

void DecisionTree::write_to_file(string filename,
  const SVec& no_th, const SVec& no_sym) const {
  string s =
    "digraph tree {\n"
    "  node [shape=box]\n" +
    dot("t", no_th, no_sym) +
    "}\n";

  ofstream f(filename);
  if (f.is_open()) {
    f << s;
    f.close();
  }
  else
    cerr << "Could not write file `" << filename << "'.\n";
}

string DecisionTree::dot(string pos,
  const SVec& no_th, const SVec& no_sym) const {
  string s;

  if (is_leaf()) {
    for (unsigned i = 0; i < labels.size(); i++) {
      string new_pos = pos + to_string(i);
      s += "  " + pos + " -> " + new_pos + "\n";
      s += "  " + new_pos + " [label = \"" + no_th[labels[i]]
                         + "\" shape = ellipse]\n";
    }
  }
  else {
    s += "  " + pos + " [label = \"" + no_sym[feature] + "\"]\n";
    s += "  " + pos + " -> " + pos + "l\n";
    s += "  " + pos + " -> " + pos + "r\n";
    s +=  left->dot(pos + "l", no_th, no_sym);
    s += right->dot(pos + "r", no_th, no_sym);
  }

  return s;
}

#endif
