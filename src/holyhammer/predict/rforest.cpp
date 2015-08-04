#ifndef RFOREST_CPP
#define RFOREST_CPP

#include <random>

#include "dtree.cpp"
#include "predictor.cpp"
#include "tfidf.cpp"

class RandomForest : public Predictor {
  public:
    RandomForest(LVecVec deps, LVecVec syms, LVecVec sym_ths, long sym_num,
      long n_trees, long n_samples, long n_features, double depweight);
    ~RandomForest();

    void import_data(string dirname);
    void export_data(string dirname) const;

    void learn(long from, long to);
    LDPairVec predict(const LVec& csyms, long maxth, long no_adv) const;

  private:
    long n_of_samples_with_label(const LVec& samples, long label) const;
    long n_of_labels_in_samples(const LVec& samples) const;
    pair<LUMap, long> labels_of_samples(const LVec& samples) const;
    double gini_part(const LVec& samples) const;
    double gini_index(const LVec& samples, long feature) const;

    LUMap features_frequency(const LVec& samples) const;
    long feature_minlabels(const LVec& samples, long feature) const;

    long best_feature_gini(const LVec& samples, unsigned min_labels,
      const LUMap& features_freq) const;
    long best_feature_naive(const LVec& samples) const;

    void update_tree(DecisionTree *tree, const LVec& samples);

    DecisionTree* grow_tree(const LVec& samples);
    DecisionTree* grow_tree(const LVec& samples, unsigned min_labels,
      const LUMap& features_freq);

    vector<DecisionTree*> forest;
    long n_samples;   // number of samples  to consider per tree
    long n_features;  // number of features to consider per tree
    double depweight;

    bool prelearned;

    Tfidf labels_ti;

    mt19937 rng;  // random number generator, in this case Mersenne twister
};

// TODO: seed hard-coded ...
RandomForest::RandomForest(LVecVec deps, LVecVec syms, LVecVec sym_ths,
  long sym_num,
  long n_trees, long n_samples, long n_features, double depweight)
: Predictor(deps, syms, sym_ths, sym_num), forest(n_trees, NULL),
  n_samples(n_samples), n_features(n_features), depweight(depweight),
  prelearned(false), labels_ti(deps.size()), rng(42) {

  for (auto& tree : forest)
    tree = new DecisionTree;
}

RandomForest::~RandomForest() {
  for (auto& tree : forest)
    delete tree;
}

void RandomForest::import_data(string dirname) {
  for (unsigned i = 0; i < forest.size(); i++)
    forest[i] = new DecisionTree(dirname + "/tree" + to_string(i) + ".dot",
      th_no, sym_no);
  prelearned = true;
}

void RandomForest::export_data(string dirname) const {
  for (unsigned i = 0; i < forest.size(); i++)
    forest[i]->write_to_file(dirname + "/tree" + to_string(i) + ".dot",
      no_th, no_sym);
}

void RandomForest::learn(long from, long to) {
  // update TF-IDF information for labels
  for (unsigned i = from; i < to; i++)
    labels_ti.add(deps[i]);

  if (prelearned)
    return;

  // by how many trees will a sample be learnt
  const long sampling_frequency = 1;

  // determine which tree should learn which samples
  LVecVec tree_samples(forest.size());
  uniform_int_distribution<> tree_distr(0, forest.size() - 1);
  for (long s = from; s < to; s++)
    for (long n = 0; n < sampling_frequency; n++)
      tree_samples[tree_distr(rng)].push_back(s);

  for (unsigned t = 0; t < forest.size(); t++)
    update_tree(forest[t], tree_samples[t]);

  /*
  // probability of sampling from the range [from, to), when we
  // draw from [0, to)
  double prob = (to - from) / double(to);
  binomial_distribution<long> bin_dist(n_samples, prob);
  uniform_int_distribution<long> uni_dist_old(0,  from - 1);
  uniform_int_distribution<long> uni_dist_new(from, to - 1);

  for (auto& tree : forest) {
    long n_new_samples = bin_dist(rng);

    // update tree if we need to consider new samples
    if (n_new_samples > 0) {
      LVec samples_old(n_samples - n_new_samples);
      LVec samples_new(n_new_samples);

      for (auto& sample : samples_old) sample = uni_dist_old(rng);
      for (auto& sample : samples_new) sample = uni_dist_new(rng);

      samples_new.insert(samples_new.end(),
        samples_old.begin(), samples_old.end());

      // regrow
      delete tree;
      tree = grow_tree(samples_new);
    }
  }
  */
}

LDPairVec RandomForest::predict(const LVec& csyms, long maxth, long no_adv)
  const {
  LDPairVec ans = LDPairVec(maxth, make_pair(0, 0));
  for (long i = 0; i < maxth; ++i) {
    ans[i].first  = i;
    ans[i].second = 0;
  }

  LDMap labels;

  for (const auto& tree : forest)
    tree->query(csyms, labels);

/*
    double tfidf_d = 1;
    for (const auto& feature : positives)
      // is a low TF-IDF better or worse?
      // if low was better, we should probably divide here!
      tfidf_d *= tfidf.get(feature);
    long tfidf_l = tfidf_d * 1000.0;
    //cout << tfidf_l << endl;
*/

  for (const auto& label : labels) {
    // this might be the case if we use a prelearned tree, and to prevent
    // suggesting theorems "from the future", we discard them
    if (label.first >= maxth)
      continue;

    ans[label.first].second += label.second; // / pow(labels_ti.get(label), 1);

    const LVec& ds = deps[label.first];
    for (const auto& dep : ds) {
        //cerr << dw / pow(labels_ti.get(dep), 3) << endl;
      ans[dep].second += depweight * label.second; // / pow(labels_ti.get(dep), 4);
    }
  }

  sort_prediction(ans, no_adv);
  return ans;
}


long RandomForest::n_of_samples_with_label(const LVec& samples, long label)
  const {
  long sum = 0;
  for (const auto& sample : samples) {
    const LVec& ds = deps[sample];
    if (sample == label || find(ds.begin(), ds.end(), label) != ds.end())
      sum++;
  }
  return sum;
}

pair<LUMap, long> RandomForest::labels_of_samples(const LVec& samples) const {
  LUMap labels;
  long n_labels = 0;
  for (const auto& sample : samples) {
    labels[sample]++;
    n_labels++;
    for (const auto& dep : deps[sample]) {
      labels[dep]++;
      n_labels++;
    }
  }
  return make_pair(labels, n_labels);
}

double RandomForest::gini_part(const LVec& samples) const {
  auto l = labels_of_samples(samples);
  LUMap labels = l.first;
  double n_labels = l.second;

  double sum = 0.0;
  for (const auto& label : labels) {
    double p = n_of_samples_with_label(samples, label.first) / n_labels;
    sum += (p - p*p) * label.second;
  }
  return samples.size() * sum;
}

double RandomForest::gini_index(const LVec& samples, long feature) const {
  LVec yes, no;
  for (const auto& sample : samples) {
    const LVec& features = syms[sample];
    if (find(features.begin(), features.end(), feature) != features.end())
      yes.push_back(sample);
    else
       no.push_back(sample);
  }
  return gini_part(yes) + gini_part(no);
}


LUMap RandomForest::features_frequency(const LVec& samples) const {
  LUMap features_freq;
  for (const auto& sample : samples)
    for (const auto& feature : syms[sample])
      features_freq[feature]++;

  return features_freq;
}

long RandomForest::feature_minlabels(const LVec& samples, long feature)
  const {
  LVec left, right;
  for (const auto& sample : samples) {
    const LVec& csyms = syms[sample];
    if (find(csyms.begin(), csyms.end(), feature) != csyms.end())
      left.push_back(sample);
    else
      right.push_back(sample);
  }

  return min(labels_of_samples(left ).second,
             labels_of_samples(right).second);
}


template <class Container, class Generator> Container
  sample_with_replacement(const Container& c, unsigned n, Generator& g) {

  // generate sorted vector of container indices
  vector<unsigned> indices(n);
  uniform_int_distribution<> distr(0, c.size() - 1);
  for (auto& i : indices) i = distr(g);
  sort(indices.begin(), indices.end());

  Container result;
  auto citr = c.cbegin();
  unsigned prev_i = 0;
  for (const auto& i : indices) {
    advance(citr, i - prev_i);
    prev_i = i;

    copy_n(citr, 1, inserter(result, result.end()));
  }
  return result;
}

long RandomForest::best_feature_gini(const LVec& samples, unsigned min_labels,
  const LUMap& features_freq) const {

  long best_f = -1;
  double best_gini = 0;

  // iterate through unique list of features
  for (const auto& f : features_freq) {
    // check if a feature even has a chance to provide a valid split
    if (feature_minlabels(samples, f.first) >= min_labels) {
      double gini = gini_index(samples, f.first);
      if (gini < best_gini || best_f == -1) {
        best_f = f.first;
        best_gini = gini;
      }
    }
  }

  return best_f;
}

long RandomForest::best_feature_naive(const LVec& samples) const {
  LUMap ff = features_frequency(samples);
  long optimal_n_samples = samples.size() / 2;

  long best_f = -1;
  long best_diff = 0;

  for (const auto& f : ff) {
    long diff = abs(f.second - optimal_n_samples);
    if (diff < best_diff || best_f == -1) {
      best_f = f.first;
      best_diff = diff;
    }
  }

  return best_f;
}

void RandomForest::update_tree(DecisionTree *tree, const LVec& new_samples) {
  if (new_samples.empty())
    return;

  for (const auto& sample : new_samples)
    for (const auto& feature : syms[sample])
      tree->features_freq[feature]++;

  tree->n_samples += new_samples.size();

  long optimal_n_samples = tree->n_samples / 2;
  long best_f = -1;
  long best_diff = 0;

  // we have to consider all features present in the tree at this point,
  // because it might be that a feature that was previously bad, now has
  // become a good splitting feature, even if it did not appear at all
  // in the new samples
  for (const auto& f : tree->features_freq) {
    long diff = abs(f.second - optimal_n_samples);
    if (diff < best_diff || best_f == -1) {
      best_f = f.first;
      best_diff = diff;
    }
  }

  LVec update_samples = new_samples;

  if (best_f != tree->feature) {
    tree->add_labels_recursively(update_samples);

    delete tree->left;
    delete tree->right;

    tree->left  = new DecisionTree;
    tree->right = new DecisionTree;
  }

  const LVec& best = sym_ths[best_f];

  LVec left, right;

  // divide samples into those which have the best feature and those who do not
  for (const auto& sample : update_samples)
    if (find(best.begin(), best.end(), sample) != best.end())
      left.push_back(sample);
    else
      right.push_back(sample);

  if (min(left .size() + tree->left ->n_samples,
          right.size() + tree->right->n_samples) < 1) {
    tree->labels = update_samples;
    tree->feature = -1;

    delete tree->left;
    delete tree->right;

    tree->left  = NULL;
    tree->right = NULL;
  }
  else {
    tree->labels = LVec();
    tree->feature = best_f;

    update_tree(tree->left ,  left);
    update_tree(tree->right, right);
  }
}

DecisionTree* RandomForest::grow_tree(const LVec& samples) {
  LUMap ff = features_frequency(samples);
  // remove too seldomly occuring features
  /*for (auto fi = ff.begin(); fi != ff.end(); )
    if (fi->second <= 3) fi = ff.erase(fi);
    else                 fi++;*/

  LUMap fs = sample_with_replacement(ff, n_features, rng);

  return grow_tree(samples, 1/*2*log(labels_of_samples(samples).second)*/, fs);
}

DecisionTree* RandomForest::grow_tree(const LVec& samples,
  unsigned min_labels, const LUMap& features_freq) {

  long best_f = best_feature_naive(samples);
  //long best_f = best_feature_gini(samples, min_labels, features_freq);
  if (best_f == -1)
    return new DecisionTree(samples);

  const LVec& best = sym_ths[best_f];

  LVec left, right;

  // divide samples into those which have the best feature and those who do not
  for (const auto& sample : samples)
    if (find(best.begin(), best.end(), sample) != best.end())
      left.push_back(sample);
    else
      right.push_back(sample);

  // stop growing tree if one of its children would be too small
  if (min(labels_of_samples(left ).second,
          labels_of_samples(right).second) < min_labels)
    return new DecisionTree(samples);
  else {
    DecisionTree *t_left  = grow_tree(left , min_labels, features_freq);
    DecisionTree *t_right = grow_tree(right, min_labels, features_freq);
    return new DecisionTree(t_left, t_right, best_f);
  }
}

#endif
