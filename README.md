# as2

## Requirements:

- [Haskell Stack build environment](https://docs.haskellstack.org/en/stable/README/ "The Haskell Tool Stack")
- active internet conenction (stack setup loads and installs a private version of GHC)
- thr generated output is comaptible with Coq 8.8.

## Short Instructions:

```
tar -xzvf as2.tar.gz
cd as2-0.1.0.0
stack setup
stack init
stack build
stack exec -- as2-exe <OPTIONS>
```

You can use ```stack install```, to later on use ```as2-exe``` instead of ```stack exec --as2-exe```.

## Description

With no options the as2 tool operates as follows:

1. reads a HOAS specification from stdin
2. prints generated well-scoped Coq code to stdout

See the spec file system for examples of the HOAS specification (examples/spec).

It is possible to specify input and output files, as well as request the intermediate dependency graph in dot format for diagnostic purposes. Per default, the tool will not silently overwrite existing files, but request for user confirmation. This can be explicitly disabled. The maxmal line width of the generated Coq code is 140 characters, but this can also be adjusted.
It is furthermore possible to choose for which prover code is generated. At the moment well-scoped Coq code (-p Coq) and unscoped Coq code (-p UCoq) are available.

To use the generated code, place the output of the tool, say `syntax.v`, and the respective header file (`fintype.v` for well-scoped syntax, `unscoped.v` for unscoped syntax) in your project directory, and import them by adding the following directive to your development (the header is sourced implicitly through the generated code file):

```
Require Export syntax.
```

The header files can be found in src/Coq.

## Examples:

Print an overview of all options:

```
stack exec -- as2-exe --help
```

Generate the code for a call-by-value variant of System F and dump to `sysf_cbv.v`. This is the example from the LFMTP'17 WIP report.

```
stack exec -- as2-exe -i specs/sysf_cbv.sig -o sysf_cbv.v
```

## Bugs, Requests, etc.

Please direct any inquiries regarding this software to `autosubst@ps.uni-saarland.de`.
