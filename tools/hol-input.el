;;; hol-input.el --- The Hol input method (based/copied from Lean)
;;;
;;; DISCLAIMER: This file is based on lean-input.el provided with the Lean theorem prover.
;;; We did minor modifications
;;
;;; Commentary:
;;
;;;; A highly customisable input method which can inherit from other
;; Quail input methods. By default the input method is geared towards
;; the input of mathematical and other symbols in Hol programs.
;;
;; Use M-x customize-group hol-input to customise this input method.
;; Note that the functions defined under "Functions used to tweak
;; translation pairs" below can be used to tweak both the key
;; translations inherited from other input methods as well as the
;; ones added specifically for this one.
;;
;; Use hol-input-show-translations to see all the characters which
;; can be typed using this input method (except for those
;; corresponding to ASCII characters).

;;; Code:

(require 'quail)

(eval-when-compile
  (require 'cl))
;; Quail is quite stateful, so be careful when editing this code.  Note
;; that with-temp-buffer is used below whenever buffer-local state is
;; modified.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Utility functions

(defun hol-input-concat-map (f xs)
  "Concat (map F XS)."
  (apply 'append (mapcar f xs)))

(defun hol-input-to-string-list (s)
  "Convert a string S to a list of one-character strings, after
removing all space and newline characters."
  (hol-input-concat-map
   (lambda (c) (if (member c (string-to-list " \n"))
              nil
            (list (string c))))
   (string-to-list s)))

(defun hol-input-character-range (from to)
  "A string consisting of the characters from FROM to TO."
  (let (seq)
    (dotimes (i (1+ (- to from)))
      (setq seq (cons (+ from i) seq)))
    (concat (nreverse seq))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Functions used to tweak translation pairs

;; lexical-let is used since Elisp lacks lexical scoping.

(defun hol-input-compose (f g)
  "\x -> concatMap F (G x)"
  (lexical-let ((f1 f) (g1 g))
    (lambda (x) (hol-input-concat-map f1 (funcall g1 x)))))

(defun hol-input-or (f g)
  "\x -> F x ++ G x"
  (lexical-let ((f1 f) (g1 g))
    (lambda (x) (append (funcall f1 x) (funcall g1 x)))))

(defun hol-input-nonempty ()
  "Only keep pairs with a non-empty first component."
  (lambda (x) (if (> (length (car x)) 0) (list x))))

(defun hol-input-prepend (prefix)
  "Prepend PREFIX to all key sequences."
  (lexical-let ((prefix1 prefix))
    (lambda (x) `((,(concat prefix1 (car x)) . ,(cdr x))))))

(defun hol-input-prefix (prefix)
  "Only keep pairs whose key sequence starts with PREFIX."
  (lexical-let ((prefix1 prefix))
    (lambda (x)
      (if (equal (substring (car x) 0 (length prefix1)) prefix1)
          (list x)))))

(defun hol-input-suffix (suffix)
  "Only keep pairs whose key sequence ends with SUFFIX."
  (lexical-let ((suffix1 suffix))
    (lambda (x)
      (if (equal (substring (car x)
                            (- (length (car x)) (length suffix1)))
                 suffix1)
          (list x)))))

(defun hol-input-drop (ss)
  "Drop pairs matching one of the given key sequences.
SS should be a list of strings."
  (lexical-let ((ss1 ss))
    (lambda (x) (unless (member (car x) ss1) (list x)))))

(defun hol-input-drop-beginning (n)
  "Drop N characters from the beginning of each key sequence."
  (lexical-let ((n1 n))
    (lambda (x) `((,(substring (car x) n1) . ,(cdr x))))))

(defun hol-input-drop-end (n)
  "Drop N characters from the end of each key sequence."
  (lexical-let ((n1 n))
    (lambda (x)
      `((,(substring (car x) 0 (- (length (car x)) n1)) .
         ,(cdr x))))))

(defun hol-input-drop-prefix (prefix)
  "Only keep pairs whose key sequence starts with PREFIX.
This prefix is dropped."
  (hol-input-compose
   (hol-input-drop-beginning (length prefix))
   (hol-input-prefix prefix)))

(defun hol-input-drop-suffix (suffix)
  "Only keep pairs whose key sequence ends with SUFFIX.
This suffix is dropped."
  (lexical-let ((suffix1 suffix))
    (hol-input-compose
     (hol-input-drop-end (length suffix1))
     (hol-input-suffix suffix1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Customization

;; The :set keyword is set to 'hol-input-incorporate-changed-setting
;; so that the input method gets updated immediately when users
;; customize it. However, the setup functions cannot be run before all
;; variables have been defined. Hence the :initialize keyword is set to
;; 'custom-initialize-default to ensure that the setup is not performed
;; until hol-input-setup is called at the end of this file.

(defgroup hol-input nil
  "The Hol input method.
After tweaking these settings you may want to inspect the resulting
translations using `hol-input-show-translations'."
  :group 'hol
  :group 'leim)

(defcustom hol-input-tweak-all
  '(hol-input-compose
    (hol-input-prepend "\\")
    (hol-input-nonempty))
  "An expression yielding a function which can be used to tweak
all translations before they are included in the input method.
The resulting function (if non-nil) is applied to every
\(KEY-SEQUENCE . TRANSLATION) pair and should return a list of such
pairs. (Note that the translations can be anything accepted by
`quail-defrule'.)

If you change this setting manually (without using the
customization buffer) you need to call `hol-input-setup' in
order for the change to take effect."
  :group 'hol-input
  :set 'hol-input-incorporate-changed-setting
  :initialize 'custom-initialize-default
  :type 'sexp)

(defcustom hol-input-inherit
  `(("TeX" . (hol-input-compose
              (hol-input-drop '("geq" "leq" "bullet" "qed" "par"))
              (hol-input-or
               (hol-input-drop-prefix "\\")
               (hol-input-or
                (hol-input-compose
                 (hol-input-drop '("^o"))
                 (hol-input-prefix "^"))
                (hol-input-prefix "_")))))
    )
  "A list of Quail input methods whose translations should be
inherited by the Hol input method (with the exception of
translations corresponding to ASCII characters).

The list consists of pairs (qp . tweak), where qp is the name of
a Quail package, and tweak is an expression of the same kind as
`hol-input-tweak-all' which is used to tweak the translation
pairs of the input method.

The inherited translation pairs are added last, after
`hol-input-user-translations' and `hol-input-translations'.

If you change this setting manually (without using the
customization buffer) you need to call `hol-input-setup' in
order for the change to take effect."
  :group 'hol-input
  :set 'hol-input-incorporate-changed-setting
  :initialize 'custom-initialize-default
  :type '(repeat (cons (string :tag "Quail package")
                       (sexp :tag "Tweaking function"))))

(defcustom hol-input-translations
  (let ((max-lisp-eval-depth 2800)) `(

  ;; Negation

  ("not" . ("¬"))

  ;; Equality and similar symbols.

  ("eq"  . ,(hol-input-to-string-list "=∼∽≈≋∻∾∿≀≃⋍≂≅ ≌≊≡≣≐≑≒≓≔≕≖≗≘≙≚≛≜≝≞≟≍≎≏≬⋕"))
  ("eqn" . ,(hol-input-to-string-list "≠≁ ≉     ≄  ≇≆  ≢                 ≭    "))
  ("equiv" . ,(hol-input-to-string-list "≃⋍"))
  ("iso" . ,(hol-input-to-string-list "≅≌"))

                    ("=n"  . ("≠"))
  ("~"    . ("∼"))  ("~n"  . ("≁")) ("homotopy"    . ("∼"))
  ("~~"   . ("≈"))  ("~~n" . ("≉"))
  ("~~~"  . ("≋"))
  (":~"   . ("∻"))
  ("~-"   . ("≃"))  ("~-n" . ("≄"))
  ("-~"   . ("≂"))
  ("~="   . ("≅"))  ("~=n" . ("≇"))
  ("~~-"  . ("≊"))
  ("=="   . ("≡"))  ("==n" . ("≢"))
  ("==="  . ("≣"))
  (".="   . ("≐"))  (".=." . ("≑"))
  (":="   . ("≔"))  ("=:"  . ("≕"))
  ("=o"   . ("≗"))
  ("(="   . ("≘"))
  ("and=" . ("≙"))  ("or=" . ("≚"))
  ("*="   . ("≛"))
  ("t="   . ("≜"))
  ("def=" . ("≝"))
  ("m="   . ("≞"))
  ("?="   . ("≟"))

  ("pr" . ("↣"))

  ("1" . ("₁"))
  ("2" . ("₂"))
  ("3" . ("₃"))
  ("4" . ("₄"))
  ("5" . ("₅"))
  ("6" . ("₆"))
  ("7" . ("₇"))
  ("8" . ("₈"))
  ("9" . ("₉"))
  ("0" . ("₀"))

  ;; Inequality and similar symbols.

  ("leq"  . ,(hol-input-to-string-list "≤≦≲<≪⋘ ≶≺≼≾⊂⊆ ⋐⊏⊑ ⊰⊲⊴⋖⋚⋜⋞"))
  ("leqn" . ,(hol-input-to-string-list "≰≨≮≴⋦   ≸⊀ ⋨⊄⊈⊊  ⋢⋤ ⋪⋬   ⋠"))
  ("geq"  . ,(hol-input-to-string-list "≥≧≳>≫⋙ ≷≻≽≿⊃⊇ ⋑⊐⊒ ⊱⊳⊵⋗⋛⋝⋟"))
  ("geqn" . ,(hol-input-to-string-list "≱≩≯≵⋧ ≹  ⊁ ⋩⊅⊉⊋  ⋣⋥ ⋫⋭   ⋡"))

  ("<="   . ("≤"))  (">="   . ("≥"))
  ("<=n"  . ("≰"))  (">=n"  . ("≱"))
  ("len"  . ("≰"))  ("gen"  . ("≱"))
  ("<n"   . ("≮"))  (">n"   . ("≯"))
  ("<~"   . ("≲"))  (">~"   . ("≳"))
  ("<~n"  . ("⋦"))  (">~n"  . ("⋧"))
  ("<~nn" . ("≴"))  (">~nn" . ("≵"))

  ("ssub"   . ("⊂"))  ("ssup"   . ("⊃"))
  ("ssubn"  . ("⊄"))  ("ssupn"  . ("⊅"))
  ("sub"  . ("⊆")) ("sup"  . ("⊇"))
  ("subn" . ("⊈")) ("supn" . ("⊉"))
  ("ssqub"   . ("⊏"))  ("ssqup"   . ("⊐"))
  ("squb"  . ("⊑"))  ("squp"  . ("⊒"))
  ("squbn" . ("⋢"))  ("squpn" . ("⋣"))

  ;; Set membership etc.

  ("member" . ,(hol-input-to-string-list "∈∉∊∋∌∍⋲⋳⋴⋵⋶⋷⋸⋹⋺⋻⋼⋽⋾⋿"))
  ("mem" . ("∈"))

  ("inn" . ("∉"))
  ("nin" . ("∌"))

  ;; Types

  ("T1" . ("Type₁"))
  ("T2" . ("Type₂"))
  ("T+" . ("Type₊"))

  ;; Intersections, unions etc.

  ("intersection" . ,(hol-input-to-string-list "∩⋂∧⋀⋏⨇⊓⨅⋒∏ ⊼      ⨉"))
  ("union"        . ,(hol-input-to-string-list "∪⋃∨⋁⋎⨈⊔⨆⋓∐⨿⊽⊻⊍⨃⊎⨄⊌∑⅀"))

  ("and" . ("∧"))  ("or"  . ("∨"))
  ("And" . ("⋀"))  ("Or"  . ("⋁"))
  ("i"   . ("∩"))  ("un"  . ("∪"))  ("u+" . ("⊎"))  ("u." . ("⊍"))
  ("I"   . ("⋂"))  ("Un"  . ("⋃"))  ("U+" . ("⨄"))  ("U." . ("⨃"))
  ("glb" . ("⊓"))  ("lub" . ("⊔"))
  ("Glb" . ("⨅"))  ("Lub" . ("⨆"))

  ;; Entailment etc.

  ("entails" . ,(hol-input-to-string-list "⊢⊣⊤⊥⊦⊧⊨⊩⊪⊫⊬⊭⊮⊯"))

  ("|-"   . ("⊢"))  ("|-n"  . ("⊬"))
  ("-|"   . ("⊣"))
  ("|="   . ("⊨"))  ("|=n"  . ("⊭"))
  ("||-"  . ("⊩"))  ("||-n" . ("⊮"))
  ("||="  . ("⊫"))  ("||=n" . ("⊯"))
  ("|||-" . ("⊪"))

  ;; Divisibility, parallelity.

  ("|"  . ("∣"))  ("|n"  . ("∤"))
  ("||" . ("∥"))  ("||n" . ("∦"))

  ;; Some symbols from logic and set theory.

  ("all" . ("∀"))
  ("ex"  . ("∃"))
  ("exn" . ("∄"))
  ("0"   . ("∅"))
  ("empty"   . ("∅"))
  ("C"   . ("∁"))
  ("powerset" . ("𝒫"))

  ;; Corners, ceilings and floors.

  ("c"  . ,(hol-input-to-string-list "⌜⌝⌞⌟⌈⌉⌊⌋"))
  ("cu" . ,(hol-input-to-string-list "⌜⌝  ⌈⌉  "))
  ("cl" . ,(hol-input-to-string-list "  ⌞⌟  ⌊⌋"))

  ("cul" . ("⌜"))  ("cuL" . ("⌈"))
  ("cur" . ("⌝"))  ("cuR" . ("⌉"))
  ("cll" . ("⌞"))  ("clL" . ("⌊"))
  ("clr" . ("⌟"))  ("clR" . ("⌋"))

  ;; Various operators/symbols.
  ("tr"        . ,(hol-input-to-string-list "⬝▹"))
  ("trans"     . ,(hol-input-to-string-list "▹⬝"))
  ("transport" . ("▹"))
  ("con"       . ("⬝"))
  ("cdot"      . ("⬝"))
  ("dot"      . ("⬝"))
  ("sy"        . ("⁻¹"))
  ("inv"       . ("⁻¹"))
  ("-1"        . ("⁻¹" "₋₁"))
  ("-1e"       . ("⁻¹ᵉ"))
  ("-1f"       . ("⁻¹ᶠ"))
  ("-1g"       . ("⁻¹ᵍ"))
  ("-1h"       . ("⁻¹ʰ"))
  ("-1i"       . ("⁻¹ⁱ"))
  ("-1m"       . ("⁻¹ᵐ"))
  ("-1o"       . ("⁻¹ᵒ"))
  ("-1r"       . ("⁻¹ʳ"))
  ("-1p"       . ("⁻¹ᵖ"))
  ("-1s"       . ("⁻¹ˢ"))
  ("-1v"       . ("⁻¹ᵛ"))
  ("-1E"       . ("⁻¹ᴱ"))
  ("-2"        . ("⁻²" "₋₂"))
  ("-2o"       . ("⁻²ᵒ"))
  ("-3"        . ("⁻³"))
  ("qed"       . ("∎"))
  ("x"         . ("×"))
  ("o"         . ("∘"))
  ("comp"      . ("∘"))
  ("."         . ("∙"))
  ("*"         . ("⋆"))
  (".+"        . ("∔"))
  (".-"        . ("∸"))
  (":"         . ("∶"))
  ("::"        . ("∷"))
  ("::-"       . ("∺"))
  ("-:"        . ("∹"))
  ("+ "        . ("⊹"))
  ("surd3"     . ("∛"))
  ("surd4"     . ("∜"))
  ("increment" . ("∆"))
  ("inf"       . ("∞"))
  ("&"         . ("⅋"))
  ("op"        . ("ᵒᵖ"))
  ("opf"       . ("ᵒᵖᶠ"))

  ;; Circled operators.

  ("o+"  . ("⊕"))
  ("o--" . ("⊖"))
  ("ox"  . ("⊗"))
  ("o/"  . ("⊘"))
  ("o."  . ("⊙"))
  ("oo"  . ("⊚"))
  ("o*"  . ("∘*" "⊛"))
  ("o="  . ("⊜"))
  ("o-"  . ("⊝"))

  ("O+"  . ("⨁"))
  ("Ox"  . ("⨂"))
  ("O."  . ("⨀"))
  ("O*"  . ("⍟"))

  ;; Boxed operators.

  ("b+" . ("⊞"))
  ("b-" . ("⊟"))
  ("bx" . ("⊠"))
  ("b." . ("⊡"))

  ;; Various symbols.

  ("integral" . ,(hol-input-to-string-list "∫∬∭∮∯∰∱∲∳"))
  ("angle"    . ,(hol-input-to-string-list "∟∡∢⊾⊿"))
  ("join"     . ,(hol-input-to-string-list "⋈⋉⋊⋋⋌⨝⟕⟖⟗"))

  ;; Arrows.
  ("iff" . ("↔")) ("imp"  . ("→"))
  ("l"  . ,(hol-input-to-string-list "←⇐⇚⇇⇆↤⇦↞↼↽⇠⇺↜⇽⟵⟸↚⇍⇷ ↹     ↢↩↫⇋⇜⇤⟻⟽⤆↶↺⟲                                     "))
  ("r"  . ,(hol-input-to-string-list "→⇒⇛⇉⇄↦⇨↠⇀⇁⇢⇻↝⇾⟶⟹↛⇏⇸⇶ ↴    ↣↪↬⇌⇝⇥⟼⟾⤇↷↻⟳⇰⇴⟴⟿ ➵➸➙➔➛➜➝➞➟➠➡➢➣➤➧➨➩➪➫➬➭➮➯➱➲➳➺➻➼➽➾⊸"))
  ("u"  . ,(hol-input-to-string-list "↑⇑⟰⇈⇅↥⇧↟↿↾⇡⇞          ↰↱➦ ⇪⇫⇬⇭⇮⇯                                           "))
  ("d"  . ,(hol-input-to-string-list "↓⇓⟱⇊⇵↧⇩↡⇃⇂⇣⇟         ↵↲↳➥ ↯                                                "))
  ("ud" . ,(hol-input-to-string-list "↕⇕   ↨⇳                                                                    "))
  ("lr" . ,(hol-input-to-string-list "↔⇔         ⇼↭⇿⟷⟺↮⇎⇹                                                        "))
  ("ul" . ,(hol-input-to-string-list "↖⇖                        ⇱↸                                               "))
  ("ur" . ,(hol-input-to-string-list "↗⇗                                         ➶➹➚                             "))
  ("dr" . ,(hol-input-to-string-list "↘⇘                        ⇲                ➴➷➘                             "))
  ("dl" . ,(hol-input-to-string-list "↙⇙                                                                         "))
  ("==>" . ("⟹")) ("nattrans" . ("⟹")) ("nat_trans" . ("⟹"))

  ("l-"  . ("←"))  ("<-"  . ("←"))  ("l="  . ("⇐"))
  ("r-"  . ("→"))  ("->"  . ("→"))  ("r="  . ("⇒"))  ("=>"  . ("⇒")) ("functor"  . ("⇒"))
  ("u-"  . ("↑"))                   ("u="  . ("⇑"))
  ("d-"  . ("↓"))                   ("d="  . ("⇓"))
  ("ud-" . ("↕"))                   ("ud=" . ("⇕"))
  ("lr-" . ("↔"))  ("<->" . ("↔"))  ("lr=" . ("⇔"))  ("<=>" . ("⇔"))
  ("ul-" . ("↖"))                   ("ul=" . ("⇖"))
  ("ur-" . ("↗"))                   ("ur=" . ("⇗"))
  ("dr-" . ("↘"))                   ("dr=" . ("⇘"))
  ("dl-" . ("↙"))                   ("dl=" . ("⇙"))

  ("l==" . ("⇚"))  ("l-2" . ("⇇"))                   ("l-r-" . ("⇆"))
  ("r==" . ("⇛"))  ("r-2" . ("⇉"))  ("r-3" . ("⇶"))  ("r-l-" . ("⇄"))
  ("u==" . ("⟰"))  ("u-2" . ("⇈"))                   ("u-d-" . ("⇅"))
  ("d==" . ("⟱"))  ("d-2" . ("⇊"))                   ("d-u-" . ("⇵"))

  ("l--"  . ("⟵"))  ("<--"  . ("⟵"))  ("l~"  . ("↜" "⇜"))
  ("r--"  . ("⟶"))  ("-->"  . ("⟶"))  ("r~"  . ("↝" "⇝" "⟿")) ("hom"  . ("⟶"))
  ("lr--" . ("⟷"))  ("<-->" . ("⟷"))  ("lr~" . ("↭"))

  ("l-n"  . ("↚"))  ("<-n"  . ("↚"))  ("l=n"  . ("⇍"))
  ("r-n"  . ("↛"))  ("->n"  . ("↛"))  ("r=n"  . ("⇏"))  ("=>n"  . ("⇏"))
  ("lr-n" . ("↮"))  ("<->n" . ("↮"))  ("lr=n" . ("⇎"))  ("<=>n" . ("⇎"))

  ("l-|"  . ("↤"))  ("ll-" . ("↞"))
  ("r-|"  . ("↦"))  ("rr-" . ("↠"))
  ("u-|"  . ("↥"))  ("uu-" . ("↟"))
  ("d-|"  . ("↧"))  ("dd-" . ("↡"))
  ("ud-|" . ("↨"))

  ("l->" . ("↢"))
  ("r->" . ("↣"))

  ("r-o" . ("⊸"))  ("-o"  . ("⊸"))

  ("dz" . ("↯"))

  ;; Ellipsis.

  ("..." . ,(hol-input-to-string-list "⋯⋮⋰⋱"))

  ;; Box-drawing characters.

  ("---" . ,(hol-input-to-string-list "─│┌┐└┘├┤┬┼┴╴╵╶╷╭╮╯╰╱╲╳"))
  ("--=" . ,(hol-input-to-string-list "═║╔╗╚╝╠╣╦╬╩     ╒╕╘╛╞╡╤╪╧ ╓╖╙╜╟╢╥╫╨"))
  ("--_" . ,(hol-input-to-string-list "━┃┏┓┗┛┣┫┳╋┻╸╹╺╻
                                        ┍┯┑┕┷┙┝┿┥┎┰┒┖┸┚┠╂┨┞╀┦┟╁┧┢╈┪┡╇┩
                                        ┮┭┶┵┾┽┲┱┺┹╊╉╆╅╄╃ ╿╽╼╾"))
  ("--." . ,(hol-input-to-string-list "╌╎┄┆┈┊
                                        ╍╏┅┇┉┋"))

  ;; Triangles.

  ;; Big/small, black/white.

  ("t"     . ,(hol-input-to-string-list "▸▹►▻◂◃◄◅▴▵▾▿◢◿◣◺◤◸◥◹"))
  ("Tr"    . ,(hol-input-to-string-list "◀◁▶▷▲△▼▽◬◭◮"))

  ("tb" . ,(hol-input-to-string-list "◂▸▴▾◄►◢◣◤◥"))
  ("tw" . ,(hol-input-to-string-list "◃▹▵▿◅▻◿◺◸◹"))

  ("Tb" . ,(hol-input-to-string-list "◀▶▲▼"))
  ("Tw" . ,(hol-input-to-string-list "◁▷△▽"))

  ;; Squares.

  ("sq"  . ,(hol-input-to-string-list "◾◽■□◼◻▣▢▤▥▦▧▨▩◧◨◩◪◫◰◱◲◳"))
  ("sqb" . ,(hol-input-to-string-list "■◼◾"))
  ("sqw" . ,(hol-input-to-string-list "□◻◽"))
  ("sq." . ("▣"))
  ("sqo" . ("▢"))

  ;; Rectangles.

  ("re"  . ,(hol-input-to-string-list "▬▭▮▯"))
  ("reb" . ,(hol-input-to-string-list "▬▮"))
  ("rew" . ,(hol-input-to-string-list "▭▯"))

  ;; Parallelograms.

  ("pa"  . ,(hol-input-to-string-list "▰▱"))
  ("pab" . ("▰"))
  ("paw" . ("▱"))

  ;; Diamonds.

  ("di"  . ,(hol-input-to-string-list "◆◇◈"))
  ("dib" . ("◆"))
  ("diw" . ("◇"))
  ("di." . ("◈"))

  ;; Circles.

  ("ci"   . ,(hol-input-to-string-list "●○◎◌◯◍◐◑◒◓◔◕◖◗◠◡◴◵◶◷⚆⚇⚈⚉"))
  ("cib"  . ("●"))
  ("ciw"  . ("○"))
  ("ci."  . ("◎"))
  ("ci.." . ("◌"))
  ("ciO"  . ("◯"))

  ;; Stars.

  ("st"   . ,(hol-input-to-string-list "⋆✦✧✶✴✹ ★☆✪✫✯✰✵✷✸"))
  ("st4"  . ,(hol-input-to-string-list "✦✧"))
  ("st6"  . ("✶"))
  ("st8"  . ("✴"))
  ("st12" . ("✹"))

  ;; Blackboard bold letters.

  ("bn"   . ("ℕ"))
  ("bz"   . ("ℤ"))
  ("bq"   . ("ℚ"))
  ("br"   . ("ℝ"))
  ("bc"   . ("ℂ"))
  ("bp"   . ("ℙ"))
  ("bb"   . ("𝔹"))
  ("bsum" . ("⅀"))

  ;; Blackboard bold numbers.

  ("b0"   . ("𝟘"))
  ("b1"   . ("𝟙"))
  ("b2"   . ("𝟚"))
  ("b3"   . ("𝟛"))
  ("b4"   . ("𝟜"))
  ("b5"   . ("𝟝"))
  ("b6"   . ("𝟞"))
  ("b7"   . ("𝟟"))
  ("b8"   . ("𝟠"))
  ("b9"   . ("𝟡"))

  ;; Parentheses.

  ("(" . ,(hol-input-to-string-list "([{⁅⁽₍〈⎴⟅⟦⟨⟪⦃〈《‹«「『【〔〖〚︵︷︹︻︽︿﹁﹃﹙﹛﹝（［｛｢"))
  (")" . ,(hol-input-to-string-list ")]}⁆⁾₎〉⎵⟆⟧⟩⟫⦄〉》›»」』】〕〗〛︶︸︺︼︾﹀﹂﹄﹚﹜﹞）］｝｣"))

  ("[[" . ("⟦"))
  ("]]" . ("⟧"))
  ("<"  . ("⟨"))
  (">"  . ("⟩"))
  ("<<" . ("⟪"))
  (">>" . ("⟫"))
  ("f<"  . ("‹"))
  ("f>"  . ("›"))
  ("f<<" . ("«"))
  ("f>>" . ("»"))
  ("{{" . ("⦃"))
  ("}}" . ("⦄"))

  ("(b" . ("⟅"))
  (")b" . ("⟆"))

  ("lbag" . ("⟅"))
  ("rbag" . ("⟆"))

  ;; lambda

  ("fun" . ("λ"))
  ("lam" . ("λ"))

  ("X" . ("⨯"))

  ;; Primes.

  ("'" . ,(hol-input-to-string-list "′″‴⁗"))
  ("`" . ,(hol-input-to-string-list "‵‶‷"))

  ;; Fractions.

  ("frac" . ,(hol-input-to-string-list "¼½¾⅓⅔⅕⅖⅗⅘⅙⅚⅛⅜⅝⅞⅟"))

  ;; Bullets.

  ("bu"  . ,(hol-input-to-string-list "•◦‣⁌⁍"))
  ("bub" . ("•"))
  ("buw" . ("◦"))
  ("but" . ("‣"))

  ;; Types
  ("nat"  . ("ℕ"))
  ("Nat"  . ("ℕ"))
  ("N"    . ("ℕ"))
  ("N-2"  . ("ℕ₋₂"))
  ("N-1"  . ("ℕ₋₁"))
  ("int"  . ("ℤ"))
  ("Int"  . ("ℤ"))
  ("Z"    . ("ℤ"))
  ("rat"  . ("ℚ"))
  ("Rat"  . ("ℚ"))
  ("Q"    . ("ℚ"))
  ("real" . ("ℝ"))
  ("Real" . ("ℝ"))
  ("R"    . ("ℝ"))
  ("Com"  . ("ℂ"))
  ("com"  . ("ℂ"))
  ("C"    . ("ℂ"))
  ("A"    . ("𝔸"))
  ("F"    . ("𝔽"))
  ("H"    . ("ℍ"))
  ("K"    . ("𝕂"))

  ("a" . ("α"))
  ("b" . ("β"))
  ("g" . ("γ"))

  ;; Musical symbols.

  ("note" . ,(hol-input-to-string-list "♩♪♫♬"))
  ("flat" . ("♭"))
  ("#"    . ("♯"))

  ;; Other punctuation and symbols.

  ("\\"         . ("\\"))
  ("en"         . ("–"))
  ("em"         . ("—"))
  ("^i"         . ("ⁱ"))
  ("^o"         . ("ᵒ"))
  ("!!"         . ("‼"))
  ("??"         . ("⁇"))
  ("?!"         . ("‽" "⁈"))
  ("!?"         . ("⁉"))
  ("die"        . ,(hol-input-to-string-list "⚀⚁⚂⚃⚄⚅"))
  ("asterisk"   . ,(hol-input-to-string-list "⁎⁑⁂✢✣✤✥✱✲✳✺✻✼✽❃❉❊❋"))
  ("8<"         . ("✂" "✄"))
  ("tie"        . ("⁀"))
  ("undertie"   . ("‿"))
  ("apl"        . ,(hol-input-to-string-list "⌶⌷⌸⌹⌺⌻⌼⌽⌾⌿⍀⍁⍂⍃⍄⍅⍆⍇⍈
                                               ⍉⍊⍋⍌⍍⍎⍏⍐⍑⍒⍓⍔⍕⍖⍗⍘⍙⍚⍛
                                               ⍜⍝⍞⍟⍠⍡⍢⍣⍤⍥⍦⍧⍨⍩⍪⍫⍬⍭⍮
                                               ⍯⍰⍱⍲⍳⍴⍵⍶⍷⍸⍹⍺⎕"))

  ;; Some combining characters.
  ;;
  ;; The following combining characters also have (other)
  ;; translations:
  ;; ̀ ́ ̂ ̃ ̄ ̆ ̇ ̈ ̋ ̌ ̣ ̧ ̱

  ("^--" . ,(hol-input-to-string-list"̅̿"))
  ("_--" . ,(hol-input-to-string-list"̲̳"))
  ("^~"  . ,(hol-input-to-string-list"̃͌"))
  ("_~"  .  (                         "̰"))
  ("^."  . ,(hol-input-to-string-list"̇̈⃛⃜"))
  ("_."  . ,(hol-input-to-string-list"̣̤"))
  ("^l"  . ,(hol-input-to-string-list"⃖⃐⃔"))
  ("^l-" .  (                         "⃖"))
  ("^r"  . ,(hol-input-to-string-list"⃗⃑⃕"))
  ("^r-" .  (                         "⃗"))
  ("^lr" .  (                         "⃡"))
  ("_lr" .  (                         "͍"))
  ("^^"  . ,(hol-input-to-string-list"̂̑͆"))
  ("_^"  . ,(hol-input-to-string-list"̭̯̪"))
  ("^v"  . ,(hol-input-to-string-list"̌̆"))
  ("_v"  . ,(hol-input-to-string-list"̬̮̺"))

  ;; Shorter forms of many greek letters plus ƛ.

  ("Ga"  . ("α"))  ("GA"  . ("Α"))
  ("Gb"  . ("β"))  ("GB"  . ("Β"))
  ("Gg"  . ("γ"))  ("GG"  . ("Γ"))
  ("Gd"  . ("δ"))  ("GD"  . ("Δ"))
  ("Ge"  . ("ε"))  ("GE"  . ("Ε"))  ("eps" . ("ε"))
  ("Gz"  . ("ζ"))  ("GZ"  . ("Ζ"))
  ;; \eta \Eta
  ("Gth" . ("θ"))  ("GTH" . ("Θ"))  ("th"  . ("θ"))
  ("Gi"  . ("ι"))  ("GI"  . ("Ι"))
  ("Gk"  . ("κ"))  ("GK"  . ("Κ"))
  ("Gl"  . ("λ"))  ("GL"  . ("Λ"))  ("Gl-" . ("ƛ"))
  ("Gm"  . ("μ"))  ("GM"  . ("Μ"))
  ("Gn"  . ("ν"))  ("GN"  . ("Ν"))
  ("Gx"  . ("ξ"))  ("GX"  . ("Ξ"))
  ;; \omicron \Omicron
  ;; \pi \Pi
  ("Gr"  . ("ρ"))  ("GR"  . ("Ρ"))
  ("Gs"  . ("σ"))  ("GS"  . ("Σ"))
  ("Gt"  . ("τ"))  ("GT"  . ("Τ"))
  ("Gu"  . ("υ"))  ("GU"  . ("Υ"))
  ("Gf"  . ("φ"))  ("GF"  . ("Φ"))
  ("Gc"  . ("χ"))  ("GC"  . ("Χ"))
  ("Gp"  . ("ψ"))  ("GP"  . ("Ψ"))
  ("Go"  . ("ω"))  ("GO"  . ("Ω"))
  ;; even shorter versions for central type constructors
  ("S"   . ("Σ"))  ("P"   . ("Π"))

  ;; Mathematical characters

  ("MiA" . ("𝐴"))
  ("MiB" . ("𝐵"))
  ("MiC" . ("𝐶"))
  ("MiD" . ("𝐷"))
  ("MiE" . ("𝐸"))
  ("MiF" . ("𝐹"))
  ("MiG" . ("𝐺"))
  ("MiH" . ("𝐻"))
  ("MiI" . ("𝐼"))
  ("MiJ" . ("𝐽"))
  ("MiK" . ("𝐾"))
  ("MiL" . ("𝐿"))
  ("MiM" . ("𝑀"))
  ("MiN" . ("𝑁"))
  ("MiO" . ("𝑂"))
  ("MiP" . ("𝑃"))
  ("MiQ" . ("𝑄"))
  ("MiR" . ("𝑅"))
  ("MiS" . ("𝑆"))
  ("MiT" . ("𝑇"))
  ("MiU" . ("𝑈"))
  ("MiV" . ("𝑉"))
  ("MiW" . ("𝑊"))
  ("MiX" . ("𝑋"))
  ("MiY" . ("𝑌"))
  ("MiZ" . ("𝑍"))
  ("Mia" . ("𝑎"))
  ("Mib" . ("𝑏"))
  ("Mic" . ("𝑐"))
  ("Mid" . ("𝑑"))
  ("Mie" . ("𝑒"))
  ("Mif" . ("𝑓"))
  ("Mig" . ("𝑔"))
  ("Mii" . ("𝑖"))
  ("Mij" . ("𝑗"))
  ("Mik" . ("𝑘"))
  ("Mil" . ("𝑙"))
  ("Mim" . ("𝑚"))
  ("Min" . ("𝑛"))
  ("Mio" . ("𝑜"))
  ("Mip" . ("𝑝"))
  ("Miq" . ("𝑞"))
  ("Mir" . ("𝑟"))
  ("Mis" . ("𝑠"))
  ("Mit" . ("𝑡"))
  ("Miu" . ("𝑢"))
  ("Miv" . ("𝑣"))
  ("Miw" . ("𝑤"))
  ("Mix" . ("𝑥"))
  ("Miy" . ("𝑦"))
  ("Miz" . ("𝑧"))
  ("MIA" . ("𝑨"))
  ("MIB" . ("𝑩"))
  ("MIC" . ("𝑪"))
  ("MID" . ("𝑫"))
  ("MIE" . ("𝑬"))
  ("MIF" . ("𝑭"))
  ("MIG" . ("𝑮"))
  ("MIH" . ("𝑯"))
  ("MII" . ("𝑰"))
  ("MIJ" . ("𝑱"))
  ("MIK" . ("𝑲"))
  ("MIL" . ("𝑳"))
  ("MIM" . ("𝑴"))
  ("MIN" . ("𝑵"))
  ("MIO" . ("𝑶"))
  ("MIP" . ("𝑷"))
  ("MIQ" . ("𝑸"))
  ("MIR" . ("𝑹"))
  ("MIS" . ("𝑺"))
  ("MIT" . ("𝑻"))
  ("MIU" . ("𝑼"))
  ("MIV" . ("𝑽"))
  ("MIW" . ("𝑾"))
  ("MIX" . ("𝑿"))
  ("MIY" . ("𝒀"))
  ("MIZ" . ("𝒁"))
  ("MIa" . ("𝒂"))
  ("MIb" . ("𝒃"))
  ("MIc" . ("𝒄"))
  ("MId" . ("𝒅"))
  ("MIe" . ("𝒆"))
  ("MIf" . ("𝒇"))
  ("MIg" . ("𝒈"))
  ("MIh" . ("𝒉"))
  ("MIi" . ("𝒊"))
  ("MIj" . ("𝒋"))
  ("MIk" . ("𝒌"))
  ("MIl" . ("𝒍"))
  ("MIm" . ("𝒎"))
  ("MIn" . ("𝒏"))
  ("MIo" . ("𝒐"))
  ("MIp" . ("𝒑"))
  ("MIq" . ("𝒒"))
  ("MIr" . ("𝒓"))
  ("MIs" . ("𝒔"))
  ("MIt" . ("𝒕"))
  ("MIu" . ("𝒖"))
  ("MIv" . ("𝒗"))
  ("MIw" . ("𝒘"))
  ("MIx" . ("𝒙"))
  ("MIy" . ("𝒚"))
  ("MIz" . ("𝒛"))
  ("McA" . ("𝒜"))
  ("McC" . ("𝒞"))
  ("McD" . ("𝒟"))
  ("McG" . ("𝒢"))
  ("McJ" . ("𝒥"))
  ("McK" . ("𝒦"))
  ("McN" . ("𝒩"))
  ("McO" . ("𝒪"))
  ("McP" . ("𝒫"))
  ("McQ" . ("𝒬"))
  ("McS" . ("𝒮"))
  ("McT" . ("𝒯"))
  ("McU" . ("𝒰"))
  ("McV" . ("𝒱"))
  ("McW" . ("𝒲"))
  ("McX" . ("𝒳"))
  ("McY" . ("𝒴"))
  ("McZ" . ("𝒵"))
  ("Mca" . ("𝒶"))
  ("Mcb" . ("𝒷"))
  ("Mcc" . ("𝒸"))
  ("Mcd" . ("𝒹"))
  ("Mcf" . ("𝒻"))
  ("Mch" . ("𝒽"))
  ("Mci" . ("𝒾"))
  ("Mcj" . ("𝒿"))
  ("Mck" . ("𝓀"))
  ("Mcl" . ("𝓁"))
  ("Mcm" . ("𝓂"))
  ("Mcn" . ("𝓃"))
  ("Mcp" . ("𝓅"))
  ("Mcq" . ("𝓆"))
  ("Mcr" . ("𝓇"))
  ("Mcs" . ("𝓈"))
  ("Mct" . ("𝓉"))
  ("Mcu" . ("𝓊"))
  ("Mcv" . ("𝓋"))
  ("Mcw" . ("𝓌"))
  ("Mcx" . ("𝓍"))
  ("Mcy" . ("𝓎"))
  ("Mcz" . ("𝓏"))
  ("MCA" . ("𝓐"))
  ("MCB" . ("𝓑"))
  ("MCC" . ("𝓒"))
  ("MCD" . ("𝓓"))
  ("MCE" . ("𝓔"))
  ("MCF" . ("𝓕"))
  ("MCG" . ("𝓖"))
  ("MCH" . ("𝓗"))
  ("MCI" . ("𝓘"))
  ("MCJ" . ("𝓙"))
  ("MCK" . ("𝓚"))
  ("MCL" . ("𝓛"))
  ("MCM" . ("𝓜"))
  ("MCN" . ("𝓝"))
  ("MCO" . ("𝓞"))
  ("MCP" . ("𝓟"))
  ("MCQ" . ("𝓠"))
  ("MCR" . ("𝓡"))
  ("MCS" . ("𝓢"))
  ("MCT" . ("𝓣"))
  ("MCU" . ("𝓤"))
  ("MCV" . ("𝓥"))
  ("MCW" . ("𝓦"))
  ("MCX" . ("𝓧"))
  ("MCY" . ("𝓨"))
  ("MCZ" . ("𝓩"))
  ("MCa" . ("𝓪"))
  ("MCb" . ("𝓫"))
  ("MCc" . ("𝓬"))
  ("MCd" . ("𝓭"))
  ("MCe" . ("𝓮"))
  ("MCf" . ("𝓯"))
  ("MCg" . ("𝓰"))
  ("MCh" . ("𝓱"))
  ("MCi" . ("𝓲"))
  ("MCj" . ("𝓳"))
  ("MCk" . ("𝓴"))
  ("MCl" . ("𝓵"))
  ("MCm" . ("𝓶"))
  ("MCn" . ("𝓷"))
  ("MCo" . ("𝓸"))
  ("MCp" . ("𝓹"))
  ("MCq" . ("𝓺"))
  ("MCr" . ("𝓻"))
  ("MCs" . ("𝓼"))
  ("MCt" . ("𝓽"))
  ("MCu" . ("𝓾"))
  ("MCv" . ("𝓿"))
  ("MCw" . ("𝔀"))
  ("MCx" . ("𝔁"))
  ("MCy" . ("𝔂"))
  ("MCz" . ("𝔃"))
  ("MfA" . ("𝔄"))
  ("MfB" . ("𝔅"))
  ("MfD" . ("𝔇"))
  ("MfE" . ("𝔈"))
  ("MfF" . ("𝔉"))
  ("MfG" . ("𝔊"))
  ("MfJ" . ("𝔍"))
  ("MfK" . ("𝔎"))
  ("MfL" . ("𝔏"))
  ("MfM" . ("𝔐"))
  ("MfN" . ("𝔑"))
  ("MfO" . ("𝔒"))
  ("MfP" . ("𝔓"))
  ("MfQ" . ("𝔔"))
  ("MfS" . ("𝔖"))
  ("MfT" . ("𝔗"))
  ("MfU" . ("𝔘"))
  ("MfV" . ("𝔙"))
  ("MfW" . ("𝔚"))
  ("MfX" . ("𝔛"))
  ("MfY" . ("𝔜"))
  ("Mfa" . ("𝔞"))
  ("Mfb" . ("𝔟"))
  ("Mfc" . ("𝔠"))
  ("Mfd" . ("𝔡"))
  ("Mfe" . ("𝔢"))
  ("Mff" . ("𝔣"))
  ("Mfg" . ("𝔤"))
  ("Mfh" . ("𝔥"))
  ("Mfi" . ("𝔦"))
  ("Mfj" . ("𝔧"))
  ("Mfk" . ("𝔨"))
  ("Mfl" . ("𝔩"))
  ("Mfm" . ("𝔪"))
  ("Mfn" . ("𝔫"))
  ("Mfo" . ("𝔬"))
  ("Mfp" . ("𝔭"))
  ("Mfq" . ("𝔮"))
  ("Mfr" . ("𝔯"))
  ("Mfs" . ("𝔰"))
  ("Mft" . ("𝔱"))
  ("Mfu" . ("𝔲"))
  ("Mfv" . ("𝔳"))
  ("Mfw" . ("𝔴"))
  ("Mfx" . ("𝔵"))
  ("Mfy" . ("𝔶"))
  ("Mfz" . ("𝔷"))

  ;; Some ISO8859-1 characters.

  (" "         . (" "))
  ("!"         . ("¡"))
  ("cent"      . ("¢"))
  ("brokenbar" . ("¦"))
  ("degree"    . ("°"))
  ("?"         . ("¿"))
  ("^a_"       . ("ª"))
  ("^o_"       . ("º"))

  ;; Circled, parenthesised etc. numbers and letters.

  ( "(0)" . ,(hol-input-to-string-list " ⓪"))
  ( "(1)" . ,(hol-input-to-string-list "⑴①⒈❶➀➊"))
  ( "(2)" . ,(hol-input-to-string-list "⑵②⒉❷➁➋"))
  ( "(3)" . ,(hol-input-to-string-list "⑶③⒊❸➂➌"))
  ( "(4)" . ,(hol-input-to-string-list "⑷④⒋❹➃➍"))
  ( "(5)" . ,(hol-input-to-string-list "⑸⑤⒌❺➄➎"))
  ( "(6)" . ,(hol-input-to-string-list "⑹⑥⒍❻➅➏"))
  ( "(7)" . ,(hol-input-to-string-list "⑺⑦⒎❼➆➐"))
  ( "(8)" . ,(hol-input-to-string-list "⑻⑧⒏❽➇➑"))
  ( "(9)" . ,(hol-input-to-string-list "⑼⑨⒐❾➈➒"))
  ("(10)" . ,(hol-input-to-string-list "⑽⑩⒑❿➉➓"))
  ("(11)" . ,(hol-input-to-string-list "⑾⑪⒒"))
  ("(12)" . ,(hol-input-to-string-list "⑿⑫⒓"))
  ("(13)" . ,(hol-input-to-string-list "⒀⑬⒔"))
  ("(14)" . ,(hol-input-to-string-list "⒁⑭⒕"))
  ("(15)" . ,(hol-input-to-string-list "⒂⑮⒖"))
  ("(16)" . ,(hol-input-to-string-list "⒃⑯⒗"))
  ("(17)" . ,(hol-input-to-string-list "⒄⑰⒘"))
  ("(18)" . ,(hol-input-to-string-list "⒅⑱⒙"))
  ("(19)" . ,(hol-input-to-string-list "⒆⑲⒚"))
  ("(20)" . ,(hol-input-to-string-list "⒇⑳⒛"))

  ("(a)"  . ,(hol-input-to-string-list "⒜Ⓐⓐ"))
  ("(b)"  . ,(hol-input-to-string-list "⒝Ⓑⓑ"))
  ("(c)"  . ,(hol-input-to-string-list "⒞Ⓒⓒ"))
  ("(d)"  . ,(hol-input-to-string-list "⒟Ⓓⓓ"))
  ("(e)"  . ,(hol-input-to-string-list "⒠Ⓔⓔ"))
  ("(f)"  . ,(hol-input-to-string-list "⒡Ⓕⓕ"))
  ("(g)"  . ,(hol-input-to-string-list "⒢Ⓖⓖ"))
  ("(h)"  . ,(hol-input-to-string-list "⒣Ⓗⓗ"))
  ("(i)"  . ,(hol-input-to-string-list "⒤Ⓘⓘ"))
  ("(j)"  . ,(hol-input-to-string-list "⒥Ⓙⓙ"))
  ("(k)"  . ,(hol-input-to-string-list "⒦Ⓚⓚ"))
  ("(l)"  . ,(hol-input-to-string-list "⒧Ⓛⓛ"))
  ("(m)"  . ,(hol-input-to-string-list "⒨Ⓜⓜ"))
  ("(n)"  . ,(hol-input-to-string-list "⒩Ⓝⓝ"))
  ("(o)"  . ,(hol-input-to-string-list "⒪Ⓞⓞ"))
  ("(p)"  . ,(hol-input-to-string-list "⒫Ⓟⓟ"))
  ("(q)"  . ,(hol-input-to-string-list "⒬Ⓠⓠ"))
  ("(r)"  . ,(hol-input-to-string-list "⒭Ⓡⓡ"))
  ("(s)"  . ,(hol-input-to-string-list "⒮Ⓢⓢ"))
  ("(t)"  . ,(hol-input-to-string-list "⒯Ⓣⓣ"))
  ("(u)"  . ,(hol-input-to-string-list "⒰Ⓤⓤ"))
  ("(v)"  . ,(hol-input-to-string-list "⒱Ⓥⓥ"))
  ("(w)"  . ,(hol-input-to-string-list "⒲Ⓦⓦ"))
  ("(x)"  . ,(hol-input-to-string-list "⒳Ⓧⓧ"))
  ("(y)"  . ,(hol-input-to-string-list "⒴Ⓨⓨ"))
  ("(z)"  . ,(hol-input-to-string-list "⒵Ⓩⓩ"))
  ("y"    . ("ɏ"))


  ))
  "A list of translations specific to the Hol input method.
Each element is a pair (KEY-SEQUENCE-STRING . LIST-OF-TRANSLATION-STRINGS).
All the translation strings are possible translations
of the given key sequence; if there is more than one you can choose
between them using the arrow keys.

Note that if you customize this setting you will not
automatically benefit (or suffer) from modifications to its
default value when the library is updated.  If you just want to
add some bindings it is probably a better idea to customize
`hol-input-user-translations'.

These translation pairs are included after those in
`hol-input-user-translations', but before the ones inherited
from other input methods (see `hol-input-inherit').

If you change this setting manually (without using the
customization buffer) you need to call `hol-input-setup' in
order for the change to take effect."
  :group 'hol-input
  :set 'hol-input-incorporate-changed-setting
  :initialize 'custom-initialize-default
  :type '(repeat (cons (string :tag "Key sequence")
                       (repeat :tag "Translations" string))))

(defcustom hol-input-user-translations nil
  "Like `hol-input-translations', but more suitable for user
customizations since by default it is empty.

These translation pairs are included first, before those in
`hol-input-translations' and the ones inherited from other input
methods."
  :group 'hol-input
  :set 'hol-input-incorporate-changed-setting
  :initialize 'custom-initialize-default
  :type '(repeat (cons (string :tag "Key sequence")
                       (repeat :tag "Translations" string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Inspecting and modifying translation maps

(defun hol-input-get-translations (qp)
  "Return a list containing all translations from the Quail
package QP (except for those corresponding to ASCII).
Each pair in the list has the form (KEY-SEQUENCE . TRANSLATION)."
  (with-temp-buffer
    (activate-input-method qp) ; To make sure that the package is loaded.
    (unless (quail-package qp)
      (error "%s is not a Quail package." qp))
    (let ((decode-map (list 'decode-map)))
      (quail-build-decode-map (list (quail-map)) "" decode-map 0)
      (cdr decode-map))))

(defun hol-input-show-translations (qp)
  "Display all translations used by the Quail package QP (a string).
\(Except for those corresponding to ASCII)."
  (interactive (list (read-input-method-name
                      "Quail input method (default %s): " "Hol")))
  (let ((buf (concat "*" qp " input method translations*")))
    (with-output-to-temp-buffer buf
      (with-current-buffer buf
        (quail-insert-decode-map
         (cons 'decode-map (hol-input-get-translations qp)))))))

(defun hol-input-add-translations (trans)
  "Add the given translations TRANS to the Hol input method.
TRANS is a list of pairs (KEY-SEQUENCE . TRANSLATION). The
translations are appended to the current translations."
  (with-temp-buffer
    (dolist (tr (hol-input-concat-map (eval hol-input-tweak-all) trans))
      (quail-defrule (car tr) (cdr tr) "Hol" t))))

(defun hol-input-inherit-package (qp &optional fun)
  "Let the Hol input method inherit the translations from the
Quail package QP (except for those corresponding to ASCII).

The optional function FUN can be used to modify the translations.
It is given a pair (KEY-SEQUENCE . TRANSLATION) and should return
a list of such pairs."
  (let ((trans (hol-input-get-translations qp)))
    (hol-input-add-translations
     (if fun (hol-input-concat-map fun trans)
       trans))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Setting up the input method

(defun hol-input-setup ()
  "Set up the Hol input method based on the customisable
variables and underlying input methods."

  ;; Create (or reset) the input method.
  (with-temp-buffer
    (quail-define-package "Hol" "UTF-8" "∏" t ; guidance
     "Hol input method.
The purpose of this input method is to edit Hol programs, but
since it is highly customisable it can be made useful for other
tasks as well."
     nil nil nil nil nil nil t ; maximum-shortest
     ))

  (hol-input-add-translations
   (mapcar (lambda (tr) (cons (car tr) (vconcat (cdr tr))))
           (append hol-input-user-translations
                   hol-input-translations)))
  (dolist (def hol-input-inherit)
    (hol-input-inherit-package (car def)
                                (eval (cdr def)))))

(defun hol-input-incorporate-changed-setting (sym val)
  "Update the Hol input method based on the customisable
variables and underlying input methods.
Suitable for use in the :set field of `defcustom'."
  (set-default sym val)
  (hol-input-setup))

;; Set up the input method.

(hol-input-setup)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Administrative details

(provide 'hol-input)
;;; hol-input.el ends here
