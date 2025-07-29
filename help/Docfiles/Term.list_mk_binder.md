## `list_mk_binder`

``` hol4
Term.list_mk_binder : term option -> term list * term -> term
```

------------------------------------------------------------------------

Performs a sequence of variable binding operations on a term.

An application `list_mk_binder (SOME c) ([v1,...,vn],M)` builds the term
`c (\v1. ... (c (\vn. M) ...))`. The term `c` should be a binder, that
is, a constant that takes a lambda abstraction and returns a bound term.
Thus `list_mk_binder` implements Church's view that variable binding
operations should be reduced to lambda-binding.

An application `list_mk_binder NONE ([v1,...,vn],M)` builds the term
`\v1...vn. M`.

### Failure

`list_mk_binder opt ([v1,...,vn],M)` fails if some `vi` `1 <= i <= n` is
not a variable. It also fails if the constructed term
`c (\v1. ... (c (\vn. M) ...))` is not well typed.

### Example

Repeated existential quantification is easy to code up using
`list_mk_binder`. For testing, we make a list of boolean variables.

``` hol4
   - fun upto b t acc = if b >= t then rev acc else upto (b+1) t (b::acc)

     fun vlist n = map (C (curry mk_var) bool o concat "v" o int_to_string)
                       (upto 0 n []);
     val vars = vlist 100;

   > val vars =
    [`v0`, `v1`, `v2`, `v3`, `v4`, `v5`, `v6`, `v7`, `v8`, `v9`, `v10`, `v11`,
     `v12`, `v13`, `v14`, `v15`, `v16`, `v17`, `v18`, `v19`, `v20`, `v21`,
     `v22`, `v23`, `v24`, `v25`, `v26`, `v27`, `v28`, `v29`, `v30`, `v31`,
     `v32`, `v33`, `v34`, `v35`, `v36`, `v37`, `v38`, `v39`, `v40`, `v41`,
     `v42`, `v43`, `v44`, `v45`, `v46`, `v47`, `v48`, `v49`, `v50`, `v51`,
     `v52`, `v53`, `v54`, `v55`, `v56`, `v57`, `v58`, `v59`, `v60`, `v61`,
     `v62`, `v63`, `v64`, `v65`, `v66`, `v67`, `v68`, `v69`, `v70`, `v71`,
     `v72`, `v73`, `v74`, `v75`, `v76`, `v77`, `v78`, `v79`, `v80`, `v81`,
     `v82`, `v83`, `v84`, `v85`, `v86`, `v87`, `v88`, `v89`, `v90`, `v91`,
     `v92`, `v93`, `v94`, `v95`, `v96`, `v97`, `v98`, `v99`] : term list
```

Now we exercise `list_mk_binder`.

``` hol4
   - val exl_tm = list_mk_binder (SOME boolSyntax.existential)
                                 (vars, list_mk_conj vars);
   > val exl_tm =
    `?v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38
      v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56
      v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74
      v75 v76 v77 v78 v79 v80 v81 v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v92
      v93 v94 v95 v96 v97 v98 v99.
       v0 /\ v1 /\ v2 /\ v3 /\ v4 /\ v5 /\ v6 /\ v7 /\ v8 /\ v9 /\ v10 /\
       v11 /\ v12 /\ v13 /\ v14 /\ v15 /\ v16 /\ v17 /\ v18 /\ v19 /\ v20 /\
       v21 /\ v22 /\ v23 /\ v24 /\ v25 /\ v26 /\ v27 /\ v28 /\ v29 /\ v30 /\
       v31 /\ v32 /\ v33 /\ v34 /\ v35 /\ v36 /\ v37 /\ v38 /\ v39 /\ v40 /\
       v41 /\ v42 /\ v43 /\ v44 /\ v45 /\ v46 /\ v47 /\ v48 /\ v49 /\ v50 /\
       v51 /\ v52 /\ v53 /\ v54 /\ v55 /\ v56 /\ v57 /\ v58 /\ v59 /\ v60 /\
       v61 /\ v62 /\ v63 /\ v64 /\ v65 /\ v66 /\ v67 /\ v68 /\ v69 /\ v70 /\
       v71 /\ v72 /\ v73 /\ v74 /\ v75 /\ v76 /\ v77 /\ v78 /\ v79 /\ v80 /\
       v81 /\ v82 /\ v83 /\ v84 /\ v85 /\ v86 /\ v87 /\ v88 /\ v89 /\ v90 /\
       v91 /\ v92 /\ v93 /\ v94 /\ v95 /\ v96 /\ v97 /\ v98 /\ v99` : term
```

### Comments

Terms with many consecutive binders should be constructed using
`list_mk_binder` and its instantiations `list_mk_abs`, `list_mk_forall`,
and `list_mk_exists`. In the current implementation of HOL, iterating
`mk_abs`, `mk_forall`, or `mk_exists` is far slower for terms with many
consecutive binders.

### See also

[`Term.list_mk_abs`](#Term.list_mk_abs),
[`boolSyntax.list_mk_forall`](#boolSyntax.list_mk_forall),
[`boolSyntax.list_mk_exists`](#boolSyntax.list_mk_exists),
[`Term.strip_binder`](#Term.strip_binder)
