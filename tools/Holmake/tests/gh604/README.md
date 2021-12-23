When Holmake does dependency analysis, it extends `INCLUDES` information by doing what is effectively a transitive closure. Thus, if the directory situation is

```
basedir: baseTheory
middir: midTheory
             Holmakefile [INCLUDES = basedir, but mid{Script,Theory} don't depend on baseTheory]
finaldir: finalTheory [depends on baseTheory]
              Holmakefile [INCLUDES = middir only]
```

then `Holmake` does the right thing. The interactive analysis does not do the transitive closure, so that interactively attempting to run `finalScript` will complain about not being able to load `baseTheory`.
