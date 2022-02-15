# TLT

TLT is a Haskell test framework oriented towards stacked monad
transformers.  TLT has no explicit test specifications.  Tests are run
where declared, with results accumulated and reported at the end.
Tests can live in an arbitrary monad transformer so long as the `TLT`
transformer is part of the stack.  Some control of the results display
is available.

See the TLT Haddock page for instructions and examples.
