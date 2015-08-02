#include <getopt.h>
#include <memory>

#include "knn.cpp"
#include "nbayes.cpp"
#include "rforest.cpp"

const string usage_str =
  "Usage: predict <syms> <deps> <seq> [OPTION]...\n"
  "\n"
  "Mandatory arguments:\n"
  "  <syms> is a file containing the symbols of theorems\n"
  "  <deps> is a file containing the dependencies of theorems\n"
  "  <seq>  is a file containing the order of theorems\n"
  "\n"
  "General options:\n"
  "  -p <method>  method is either knn, nbayes, or rforest\n"
  "  -n <i>       i is the number of predictions to output\n"
  "  -e <eval>    eval is an optional file, containing theorems for which we want predictions\n"
  "  -x <path>    eXport learned predictor data to path\n"
  "  -y <path>    Ymport learned predictor data from path\n"
  "\n"
  "Predictor-specific options:\n"
  " Random Forest:\n"
  "  -t <n>       number of trees to build\n"
  "  -s <n>       number of samples to consider per tree\n"
  "  -f <n>       number of features to consider per tree\n"
  "  -w <n>       dependency weight\n";


void print_prediction(LDPairVec prediction, long n_predictions,
  vector<string> no_th) {
  for (long j = 0; j < n_predictions; ++j) {
    // print label
    cout << no_th[prediction[j].first] << " ";
    // print weight
    //cout << "(" << prediction[j].second << ") ";
  }
  cout << endl;
}

void interaction(unique_ptr<Predictor>& p, long predno,
  const SLMap& sym_no, const vector<string>& no_th) {
  p->learn_all();
  cerr << "Learning done; awaiting your features ..." << endl;

  string line;
  while (getline(cin, line)) {
    const LVec symsi = parse_feature_list(line.begin(), line.end(), sym_no);
    long no_adv = min((long)no_th.size(), predno);
    const LDPairVec ans = p->predict(symsi, no_th.size(), no_adv);
    print_prediction(ans, no_adv, no_th);
  }
}

void evaluation(unique_ptr<Predictor>& p, string evalf, long predno,
  SLMap th_no, vector<string> no_th) {
  unordered_set<long> eval;
  read_eval(evalf, th_no, eval);

  // last theorem up to which we learnt
  long prev = 0;

  for (long i = 0; i < (long)no_th.size(); ++i) {
    if (eval.find(i) != eval.end()) {
      p->learn(prev, i);
      prev = i;

      long no_adv = min(i, predno);
      LDPairVec ans = p->predict(i, i, no_adv);

      cout << no_th[i] << ":";
      print_prediction(ans, no_adv, no_th);
    }
  }
}

int atoi_check(const char *nptr, const char *desc) {
  int result = atoi(nptr);
  if (result == 0) {
    cerr << "Error: You have to specify a valid " << desc << "!\n";
    exit(EXIT_FAILURE);
  }
  else
    return result;
}

double atof_check(const char *nptr, const char *desc) {
  double result = atof(nptr);
  if (result == 0.0) {
    cerr << "Error: You have to specify a valid " << desc << "!\n";
    exit(EXIT_FAILURE);
  }
  else
    return result;
}

int main(int argc, char* argv[]) {
  const int MIN_ARGS = 3;
  if (argc < MIN_ARGS + 1) {
    cerr << usage_str;
    return EXIT_FAILURE;
  }

  // obligatory files
  string symsf(argv[1]), depsf(argv[2]), seqf(argv[3]);

  // evaluation file
  string evalf = "";
  // number of predictions to output
  long predno = 1000;
  // prediction method
  string method = "knn";
  // path to prelearned predictor data
  string import_path, export_path;

  // Random Forest specific options
  long n_trees = 512;
  long n_samples = 512;
  long n_features = 128;
  double depweight = 1.7;

  char c;
  optind = MIN_ARGS;  // start getopt after obligatory arguments
  while ((c = getopt (argc, argv, "he:n:p:k:t:s:f:w:x:y:")) != -1)
    switch (c) {
      case 'h':
        cout << usage_str;
        return EXIT_SUCCESS;
      case 'e':
        evalf = optarg;
        break;
      case 'n':
        predno = atoi_check(optarg, "number of predictions");
        break;
      case 'p':
        method = optarg;
        break;
      case 'x':
        export_path = optarg;
        break;
      case 'y':
        import_path = optarg;
        break;
      case 't':
        n_trees = atoi_check(optarg, "number of trees");
        break;
      case 's':
        n_samples = atoi_check(optarg, "number of samples per tree");
        break;
      case 'f':
        n_features = atoi_check(optarg, "number of features per tree");
        break;
      case 'w':
        depweight = atof_check(optarg, "dependency weight");
        break;
      case '?':
        // unknown option or option lacking an argument
        // getopt prints an error message (unless opterr is set to 0)
        cerr << "Try '" << argv[0] << " -h' for more information.\n";
        return EXIT_FAILURE;
    }

  long sym_num = 0;
  SLMap th_no,           // maps a theorem to its numeric identifier
        sym_no;          // maps a  symbol to its numeric identifier
  vector<string> no_th,  // theorem name table
                 no_sym;
  LVecVec deps,          // dependencies of each theorem
          syms,          // syms[t] holds the symbols of a theorem t
          sym_ths;       // sym_ths[s] holds the theorems which contain s

  read_order(seqf, th_no, no_th);

  deps  = LVecVec(no_th.size(), vector<long>(0));
  syms  = LVecVec(no_th.size(), vector<long>(0));

  read_deps(depsf, th_no, deps);
  read_syms(symsf, syms, sym_ths, sym_num, th_no, sym_no, no_sym);

  // getting number of a theorem
  //cout << th_no["Set.subsetI"] << endl;

  // initialise predictor
  unique_ptr<Predictor> predictor;
  if (method == "knn")
    predictor.reset(new kNN(deps, syms, sym_ths, sym_num));
  else if (method == "nbayes")
    predictor.reset(new NaiveBayes(deps, syms, sym_ths, sym_num));
  else if (method == "rforest")
    predictor.reset(new RandomForest(deps, syms, sym_ths, sym_num,
      n_trees, n_samples, n_features, depweight));
  else {
    cerr << "Error: You have to specify a valid predictor!\n";
    return EXIT_FAILURE;
  }

  predictor->set_tables(no_th, no_sym, th_no, sym_no);
  if (!import_path.empty())
    predictor->import_data(import_path);

  // if user did not supply evaluation file
  if (evalf == "")
    interaction(predictor, predno, sym_no, no_th);
  else
    evaluation(predictor, evalf, predno, th_no, no_th);

  if (!export_path.empty())
    predictor->export_data(export_path);
}
