# Non-updateable thunks

## Main introduction

TODO

## Other resources

* "Sharing, Space Leaks, and Conduit and friends"
  ([well-typed.com](https://www.well-typed.com/blog/2016/09/sharing-conduit/)).
  Edsko's blog post that introduced the problem to the world.

* "The case for call-by-name"
  ([pdf](resources/ifl2024-sharing.pdf)).
  Keynote presentation at the Implementation of Functional Languages (IFL) 2024
  by Edsko de Vries.

* "Allow explicit control of sharing for user defined types"
  ([gitlab](https://gitlab.haskell.org/ghc/ghc/-/work_items/27114)).
  GHC work item opened by Andreas Klebinger discussing some of this idea.

* "PoC for #27114 - Allow explicit control of sharing for user defined types."
  ([gitlab](https://gitlab.haskell.org/ghc/ghc/-/merge_requests/15871)).
  Proof of concept implementation in ghc by Andreas, using a pragma to tag
  types; does not work correctly for polymorphic functions.

* `dupIO` package
  ([github](https://github.com/well-typed/dupIO), [hackage](https://hackage.haskell.org/package/dupIO)).
  This is another work-around, available without any ghc modifications, to
  something _like_ non-updateable thunks (but not quite).

* "Undoing unwanted sharing in Haskell: An STG transformation"
  ([external](https://docta.ucm.es/entities/publication/19629ad4-bb69-421e-8c54-40a6a87eef39)).
  Master's thesis by Javier Sagredo.

