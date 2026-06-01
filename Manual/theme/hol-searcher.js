'use strict';

/* global Mark, elasticlunr, path_to_root */

/* HOL custom searcher: a drop-in replacement for mdbook's bundled
 * searcher.js (Manual/theme/ overrides the default).  Instead of
 * querying only the current book's index, this version sequentially
 * loads each sibling book's searchindex.js on first activation,
 * keeps them in three separate elasticlunr.Index objects, queries
 * all three on every input, and renders results grouped by book
 * with the current book's group first.
 *
 * Stable per-book filenames matter: each book's mdbook build emits
 * `searchindex-<hash>.js`, and the hash changes whenever content
 * does.  We expect each `Manual/book/<Book>/Holmakefile` to also
 * create a hash-free `searchindex.js` symlink alongside, so this
 * code can fetch `../<Sibling>/searchindex.js` at a fixed URL.
 *
 * Search options (boost, expand, bool) are read from each book's
 * own index, so per-book tuning (if anyone adds it later via
 * book.toml) carries through.
 */

window.search = window.search || {};
(function search() {

  if (!Mark || !elasticlunr) return;

  if (!String.prototype.startsWith) {
    String.prototype.startsWith = function(s, pos) {
      return this.substr(!pos || pos < 0 ? 0 : +pos, s.length) === s;
    };
  }

  /* ----- shared site config ----- */
  /* HOL_MANUALS is defined in Manual/theme/index.hbs near the top
   * of <head>.  Fall back to the canonical three-book list if it's
   * absent (older cache / theme override break). */
  const HOL_MANUALS =
    (window.HOL_MANUALS && window.HOL_MANUALS.books) ||
    ['Description', 'Tutorial', 'Reference'];

  /* Detect the current book from the URL path -- the same trick the
   * manual-switcher in index.hbs uses.  If we can't identify a
   * known book in the path (e.g., previewing under an odd local
   * server layout), default to whichever HOL_MANUALS lists first
   * so the cross-book search still works; the current-book-first
   * ordering is just less meaningful. */
  function detectCurrentBook() {
    const segs = window.location.pathname.split('/');
    for (const b of HOL_MANUALS) {
      if (segs.indexOf(b) !== -1) return b;
    }
    return HOL_MANUALS[0];
  }
  const currentBook = detectCurrentBook();

  /* Order books for result display: current book first, then the
   * rest in HOL_MANUALS order. */
  const displayBooks = [currentBook].concat(
    HOL_MANUALS.filter(b => b !== currentBook));

  /* ----- DOM hooks (same ids as mdbook's bundled searcher) ----- */
  const search_wrap = document.getElementById('mdbook-search-wrapper');
  const searchbar_outer =
    document.getElementById('mdbook-searchbar-outer');
  const searchbar = document.getElementById('mdbook-searchbar');
  const searchresults =
    document.getElementById('mdbook-searchresults');
  const searchresults_outer =
    document.getElementById('mdbook-searchresults-outer');
  const searchresults_header =
    document.getElementById('mdbook-searchresults-header');
  const searchicon = document.getElementById('mdbook-search-toggle');
  const content = document.getElementById('mdbook-content');

  const mark_exclude = ['text'];
  const marker = new Mark(content);
  const URL_SEARCH_PARAM = 'search';
  const URL_MARK_PARAM = 'highlight';

  /* Per-book state.  After lazy load:
   *   bookIndexes[book] = {
   *     index:           elasticlunr Index object,
   *     doc_urls:        string[],
   *     search_options:  {bool, expand, fields:{title,body,...}},
   *     results_options: {teaser_word_count, limit_results}
   *   }
   * Books missing from this map (because the corresponding
   * searchindex.js wasn't reachable) are silently skipped during
   * queries; the user sees a warning in the console only. */
  const bookIndexes = {};
  let allIndicesLoaded = false;
  let teaser_count = 0;
  let current_searchterm = '';

  /* ----- utility helpers (largely lifted from mdbook's bundled
   * searcher to keep behaviour the user already knows) ----- */

  function hasFocus() {
    return searchbar === document.activeElement;
  }

  function removeChildren(elem) {
    while (elem.firstChild) elem.removeChild(elem.firstChild);
  }

  function parseURL(url) {
    const a = document.createElement('a');
    a.href = url;
    return {
      source: url,
      protocol: a.protocol.replace(':', ''),
      host: a.hostname,
      port: a.port,
      params: (function() {
        const ret = {};
        const seg = a.search.replace(/^\?/, '').split('&');
        for (const part of seg) {
          if (!part) continue;
          const s = part.split('=');
          ret[s[0]] = s[1];
        }
        return ret;
      })(),
      file: (a.pathname.match(/\/([^/?#]+)$/i) || ['', ''])[1],
      hash: a.hash.replace('#', ''),
      path: a.pathname.replace(/^([^/])/, '/$1'),
    };
  }

  function renderURL(urlobject) {
    let url = urlobject.protocol + '://' + urlobject.host;
    if (urlobject.port !== '') url += ':' + urlobject.port;
    url += urlobject.path;
    let joiner = '?';
    for (const prop in urlobject.params) {
      if (Object.prototype.hasOwnProperty.call(urlobject.params, prop)) {
        url += joiner + prop + '=' + urlobject.params[prop];
        joiner = '&';
      }
    }
    if (urlobject.hash !== '') url += '#' + urlobject.hash;
    return url;
  }

  const escapeHTML = (function() {
    const MAP = {'&': '&amp;', '<': '&lt;', '>': '&gt;',
                 '"': '&#34;', '\'': '&#39;'};
    return function(s) {
      return s.replace(/[&<>'"]/g, c => MAP[c]);
    };
  })();

  function formatSearchMetric(count, searchterm) {
    if (count === 1) {
      return '1 search result for \'' + searchterm + '\':';
    } else if (count === 0) {
      return 'No search results for \'' + searchterm + '\'.';
    }
    return count + ' search results for \'' + searchterm + '\':';
  }

  /* Compute the cross-book href for a result.  `doc_url` is what
   * the book's `doc_urls[result.ref]` returned (always relative
   * to the book's root, e.g. `foo.html#section`).  When the
   * result is from the current book, just prepend `path_to_root`;
   * for a sibling book, also prepend `../<Book>/`.  `path_to_root`
   * is set by mdbook in <head>; in practice it's an empty string
   * for top-level book pages. */
  function bookHref(book, doc_url, encoded_search) {
    const url = doc_url.split('#');
    if (url.length === 1) url.push('');
    const fragment = '#' + url[1];
    const file = url[0];
    const prefix =
      (book === currentBook) ?
      path_to_root :
      path_to_root + '../' + book + '/';
    return prefix + file + '?' + URL_MARK_PARAM + '=' +
           encoded_search + fragment;
  }

  function formatSearchResult(book, result, searchterms) {
    const bookCfg = bookIndexes[book];
    const teaser =
      makeTeaser(escapeHTML(result.doc.body), searchterms,
                 bookCfg.results_options);
    teaser_count++;

    const encoded_search =
      encodeURIComponent(searchterms.join(' ')).replace(/'/g, '%27');

    const href =
      bookHref(book, bookCfg.doc_urls[result.ref], encoded_search);

    return '<a href="' + href +
      '" aria-details="mdbook-teaser_' + teaser_count + '">' +
      result.doc.breadcrumbs + '</a>' +
      '<span class="teaser" id="mdbook-teaser_' + teaser_count +
      '" aria-label="Search Result Teaser">' + teaser + '</span>';
  }

  /* Teaser builder -- identical algorithm to mdbook's bundled
   * searcher, just takes `results_options` as an explicit arg so
   * per-book settings can vary. */
  function makeTeaser(body, searchterms, results_options) {
    const stemmed_searchterms = searchterms.map(w =>
      elasticlunr.stemmer(w.toLowerCase()));
    const searchterm_weight = 40;
    const weighted = [];
    const sentences = body.toLowerCase().split('. ');
    let index = 0;
    let value = 0;
    let searchterm_found = false;
    for (const sentenceindex in sentences) {
      const words = sentences[sentenceindex].split(' ');
      value = 8;
      for (const wordindex in words) {
        const word = words[wordindex];
        if (word.length > 0) {
          for (const sti in stemmed_searchterms) {
            if (elasticlunr.stemmer(word).startsWith(
                stemmed_searchterms[sti])) {
              value = searchterm_weight;
              searchterm_found = true;
            }
          }
          weighted.push([word, value, index]);
          value = 2;
        }
        index += word.length + 1;
      }
      index += 1;
    }
    if (weighted.length === 0) return body;

    const window_weight = [];
    const window_size =
      Math.min(weighted.length, results_options.teaser_word_count);
    let cur_sum = 0;
    for (let i = 0; i < window_size; i++) cur_sum += weighted[i][1];
    window_weight.push(cur_sum);
    for (let i = 0; i < weighted.length - window_size; i++) {
      cur_sum -= weighted[i][1];
      cur_sum += weighted[i + window_size][1];
      window_weight.push(cur_sum);
    }

    let max_sum_window_index = 0;
    if (searchterm_found) {
      let max_sum = 0;
      for (let i = window_weight.length - 1; i >= 0; i--) {
        if (window_weight[i] > max_sum) {
          max_sum = window_weight[i];
          max_sum_window_index = i;
        }
      }
    }

    const teaser_split = [];
    index = weighted[max_sum_window_index][2];
    for (let i = max_sum_window_index;
         i < max_sum_window_index + window_size; i++) {
      const word = weighted[i];
      if (index < word[2]) {
        teaser_split.push(body.substring(index, word[2]));
        index = word[2];
      }
      if (word[1] === searchterm_weight) teaser_split.push('<em>');
      index = word[2] + word[0].length;
      teaser_split.push(body.substring(word[2], index));
      if (word[1] === searchterm_weight) teaser_split.push('</em>');
    }
    return teaser_split.join('');
  }

  /* ----- lazy index loader ----- */

  /* Each book's searchindex.js does
   *   window.search = Object.assign(window.search, JSON.parse(...))
   * so we load them sequentially: clear window.search, await load,
   * snapshot, repeat.  Parallel loading would race on window.search
   * since the three scripts target the same global. */
  function loadScript(src) {
    return new Promise((resolve, reject) => {
      const script = document.createElement('script');
      script.src = src;
      script.async = true;
      script.onload = resolve;
      script.onerror = () => reject(new Error('failed to load ' + src));
      document.head.appendChild(script);
    });
  }

  async function loadAllIndices() {
    if (allIndicesLoaded) return;
    searchbar_outer.classList.add('searching');
    for (const book of HOL_MANUALS) {
      const src = (book === currentBook) ?
        path_to_root + 'searchindex.js' :
        path_to_root + '../' + book + '/searchindex.js';
      try {
        window.search = {};
        await loadScript(src);
        const cfg = window.search;
        bookIndexes[book] = {
          index: elasticlunr.Index.load(cfg.index),
          doc_urls: cfg.doc_urls,
          search_options: cfg.search_options,
          results_options: cfg.results_options,
        };
      } catch (err) {
        console.warn('HOL searcher: skipping ' + book +
                     ' (' + err.message + ')');
      }
    }
    allIndicesLoaded = true;
    searchbar_outer.classList.remove('searching');

    /* If the user already typed something while loading, run the
     * deferred search now. */
    searchbar.focus();
    const searchterm = searchbar.value.trim();
    if (searchterm !== '') {
      searchbar.classList.add('active');
      doSearch(searchterm);
    }
  }

  /* ----- search dispatch + render ----- */

  function doSearch(searchterm) {
    if (current_searchterm === searchterm) return;
    if (!allIndicesLoaded) return;
    current_searchterm = searchterm;

    searchbar_outer.classList.add('searching');
    const searchterms = searchterm.split(' ');
    removeChildren(searchresults);
    teaser_count = 0;

    /* Run query across every loaded book; cap per-book results
     * using each book's own results_options.limit_results so the
     * Reference manual (which has 1,613 entries) doesn't drown
     * out everything else. */
    let totalRendered = 0;
    for (const book of displayBooks) {
      const cfg = bookIndexes[book];
      if (!cfg) continue;
      const results = cfg.index.search(searchterm, cfg.search_options);
      const cap =
        Math.min(results.length, cfg.results_options.limit_results);
      if (cap === 0) continue;

      const header = document.createElement('li');
      header.className = 'hol-book-group';
      header.textContent = book +
        (book === currentBook ? ' (this manual)' : '');
      searchresults.appendChild(header);

      for (let i = 0; i < cap; i++) {
        const li = document.createElement('li');
        li.innerHTML = formatSearchResult(book, results[i], searchterms);
        searchresults.appendChild(li);
        totalRendered++;
      }
    }

    searchresults_header.innerText =
      formatSearchMetric(totalRendered, searchterm);
    showResults(true);
    searchbar_outer.classList.remove('searching');
  }

  /* ----- show/hide + URL sync (same behaviour as bundled
   * searcher, just adapted to triggering loadAllIndices instead of
   * loadSearchScript) ----- */

  function showSearch(yes) {
    if (yes) {
      loadAllIndices();
      search_wrap.classList.remove('hidden');
      searchicon.setAttribute('aria-expanded', 'true');
    } else {
      search_wrap.classList.add('hidden');
      searchicon.setAttribute('aria-expanded', 'false');
      const results = searchresults.children;
      for (let i = 0; i < results.length; i++) {
        results[i].classList.remove('focus');
      }
    }
  }

  function showResults(yes) {
    if (yes) searchresults_outer.classList.remove('hidden');
    else searchresults_outer.classList.add('hidden');
  }

  function unfocusSearchbar() {
    const tmp = document.createElement('input');
    tmp.setAttribute('style', 'position: absolute; opacity: 0;');
    searchicon.appendChild(tmp);
    tmp.focus();
    tmp.remove();
  }

  function searchIconClickHandler() {
    if (search_wrap.classList.contains('hidden')) {
      showSearch(true);
      window.scrollTo(0, 0);
      searchbar.select();
    } else {
      showSearch(false);
    }
  }

  function searchbarKeyUpHandler() {
    const searchterm = searchbar.value.trim();
    if (searchterm !== '') {
      searchbar.classList.add('active');
      doSearch(searchterm);
    } else {
      searchbar.classList.remove('active');
      showResults(false);
      removeChildren(searchresults);
      current_searchterm = '';
    }
    setSearchUrlParameters(searchterm,
                           'push_if_new_search_else_replace');
    marker.unmark();
  }

  function setSearchUrlParameters(searchterm, action) {
    const url = parseURL(window.location.href);
    const first_search =
      !Object.prototype.hasOwnProperty.call(url.params, URL_SEARCH_PARAM);
    if (searchterm !== '' || action === 'push_if_new_search_else_replace') {
      url.params[URL_SEARCH_PARAM] = searchterm;
      delete url.params[URL_MARK_PARAM];
      url.hash = '';
    } else {
      delete url.params[URL_MARK_PARAM];
      delete url.params[URL_SEARCH_PARAM];
    }
    if (action === 'push' ||
        action === 'push_if_new_search_else_replace' && first_search) {
      history.pushState({}, document.title, renderURL(url));
    } else if (action === 'replace' ||
        action === 'push_if_new_search_else_replace' && !first_search) {
      history.replaceState({}, document.title, renderURL(url));
    }
  }

  function globalKeyHandler(e) {
    if (e.altKey || e.ctrlKey || e.metaKey || e.shiftKey ||
        e.target.type === 'textarea' || e.target.type === 'text' ||
        !hasFocus() &&
          /^(?:input|select|textarea)$/i.test(e.target.nodeName)) {
      return;
    }
    if (e.key === 'Escape') {
      e.preventDefault();
      searchbar.classList.remove('active');
      setSearchUrlParameters('',
        searchbar.value.trim() !== '' ? 'push' : 'replace');
      if (hasFocus()) unfocusSearchbar();
      showSearch(false);
      marker.unmark();
    } else if (!hasFocus() && (e.key === 's' || e.key === '/')) {
      e.preventDefault();
      showSearch(true);
      window.scrollTo(0, 0);
      searchbar.select();
    } else if (hasFocus() &&
               (e.key === 'ArrowDown' || e.key === 'Enter')) {
      e.preventDefault();
      /* Skip past book-group headers when arrow-navigating
       * down. */
      let first = searchresults.firstElementChild;
      while (first &&
             first.classList.contains('hol-book-group')) {
        first = first.nextElementSibling;
      }
      if (first !== null) {
        unfocusSearchbar();
        first.classList.add('focus');
        if (e.key === 'Enter') {
          window.location.assign(first.querySelector('a'));
        }
      }
    } else if (!hasFocus() && (e.key === 'ArrowDown' ||
               e.key === 'ArrowUp' || e.key === 'Enter')) {
      const focused = searchresults.querySelector('li.focus');
      if (!focused) return;
      e.preventDefault();
      if (e.key === 'ArrowDown') {
        let next = focused.nextElementSibling;
        while (next && next.classList.contains('hol-book-group')) {
          next = next.nextElementSibling;
        }
        if (next) {
          focused.classList.remove('focus');
          next.classList.add('focus');
        }
      } else if (e.key === 'ArrowUp') {
        focused.classList.remove('focus');
        let prev = focused.previousElementSibling;
        while (prev && prev.classList.contains('hol-book-group')) {
          prev = prev.previousElementSibling;
        }
        if (prev) prev.classList.add('focus');
        else searchbar.select();
      } else {
        window.location.assign(focused.querySelector('a'));
      }
    }
  }

  function doSearchOrMarkFromUrl() {
    const url = parseURL(window.location.href);
    if (Object.prototype.hasOwnProperty.call(url.params, URL_SEARCH_PARAM)
        && url.params[URL_SEARCH_PARAM] !== '') {
      showSearch(true);
      searchbar.value = decodeURIComponent(
        (url.params[URL_SEARCH_PARAM] + '').replace(/\+/g, '%20'));
      /* doSearch is gated on allIndicesLoaded; the load completion
       * path in loadAllIndices() re-runs the deferred search.  Just
       * trigger the URL-sync side-effect now. */
      searchbarKeyUpHandler();
    } else {
      showSearch(false);
    }
    if (Object.prototype.hasOwnProperty.call(url.params, URL_MARK_PARAM)) {
      const words =
        decodeURIComponent(url.params[URL_MARK_PARAM]).split(' ');
      marker.mark(words, {exclude: mark_exclude});
      const markers = document.querySelectorAll('mark');
      const hide = () => {
        for (let i = 0; i < markers.length; i++) {
          markers[i].classList.add('fade-out');
          window.setTimeout(() => marker.unmark(), 300);
        }
      };
      for (let i = 0; i < markers.length; i++) {
        markers[i].addEventListener('click', hide);
      }
    }
  }

  function initSearchInteractions() {
    searchicon.addEventListener('click',
      () => searchIconClickHandler(), false);
    searchbar.addEventListener('keyup',
      () => searchbarKeyUpHandler(), false);
    document.addEventListener('keydown',
      e => globalKeyHandler(e), false);
    window.onpopstate = () => doSearchOrMarkFromUrl();
    document.addEventListener('submit',
      e => e.preventDefault(), false);
    doSearchOrMarkFromUrl();
    window.search.hasFocus = hasFocus;
  }

  initSearchInteractions();
  window.search.hasFocus = hasFocus;
})();
