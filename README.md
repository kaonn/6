Depends on `sml-typed-abts`.
Change the path of dependencies in `cbpv.cm` to where `sml-typed-abts` is installed.
    
    rlwrap sml
    CM.make "cbpv.cm";

The prompt `>` can directly parse a computation e.g. `ret(0)` 
or load from a file e.g. `load arith`.
