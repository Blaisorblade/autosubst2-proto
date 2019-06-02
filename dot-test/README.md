# Dot example

This directory applies Autosubst2 on a specification of Dependent Object Types
(DOT), the core calculus of Scala.

This specification also shows a bug in Autosubst2, which is fixed by a one-line fix.

Code generated with:
```
$ stack exec -- as2-exe -i dotsyn.lf -p UCoq -o dotunscoped_orig.v
$ stack exec -- as2-exe -i dotsyn.lf -o dotscoped_orig.v
$ ln -s ../src/Coq/*.v .
```

The generated output refers to existing types, so it doesn't compile, but that's fixed in
`dotscoped.v` and `dotunscoped.v` by prepending a few lines.
