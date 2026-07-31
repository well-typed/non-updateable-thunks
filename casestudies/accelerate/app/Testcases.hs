-- | Test terms for sharing recovery
--
-- Each term pins down a /distinct/ failure mode. Where possible the term is
-- chosen so that the /original/ program is total, so that a runtime exception is
-- evidence of a mis-placed (or mis-hoisted) binding rather than an artefact of an
-- unguarded 'EMod'. Terms where that isn't possible are marked STRUCTURAL: for
-- those, inspect the term, don't run it.
--
-- NOTE: '-fno-cse' is essential. We construct sharing by hand, using Haskell
-- @let@/@where@ bindings; CSE would merge terms we deliberately kept apart.
{-# OPTIONS_GHC -fno-cse #-}

module Testcases (
    t0
  , t1
  , t2
  , t3
  , t4
  , t5
  , t6
  , t7
  , t8
  ) where

import MiniAccelerate

{-------------------------------------------------------------------------------
  t0: no sharing at all

  The <https://github.com/AccelerateHS/accelerate-llvm/issues/116> example
  /without/ CSE: the two branches are separate heap objects, so nothing is
  shared, no binding is introduced, and the guards do their job.

  Expect: no 'ELet' anywhere; runs clean.
-------------------------------------------------------------------------------}

t0 :: Acc () [(Int, Int)]
t0 = Generate () 4 "i" $
    EPair ()
      (EUnlessZero () (EVar () "i") (EMod () (ELit () (LInt 10)) (EVar () "i")))
      (EUnlessZero () (EVar () "i") (EMod () (ELit () (LInt 10)) (EVar () "i")))

{-------------------------------------------------------------------------------
  t1: unbound variable

  @x@ has three use sites, @n@ has two, and — the point — @n@'s definition
  mentions @x@. So the two definitions are bound at the same node and their order
  matters: @x@ must be outermost.

  Expect: @let x = 7 in let n = x mod x in ((n, x), n)@, i.e. @[((0,7),0)]@.

  Fails as: @x@ marked shared but never bound (@unbound VarSys ..@) when
  @needs@ is not transitively closed; or @x@ bound /inside/ @n@ when co-located
  definitions are ordered by heap id rather than by dependency.
-------------------------------------------------------------------------------}

t1 :: Acc () [((Int, Int), Int)]
t1 = Generate () 4 "i" $
    EPair () (EPair () n x) n
  where
    x = ELit () (LInt 7)
    n = EMod () x x

{-------------------------------------------------------------------------------
  t2: uses straddling two fragments

  @x@ is used once directly and once inside @t@'s definition, so its use sites lie
  in /two different/ fragments: one in the root, one inside @t@. It therefore
  cannot be deferred into either, and must be bound in the root, above @t@.

  Expect: @let x = 7 in ((let t = i mod x in (t, t)), x)@.

  This is the term that shows a purely local notion of "what does this fragment
  mention" cannot drive a single top-down pass: at the root, the left branch
  mentions only @t@, so nothing would be bound there, and by the time we discover
  that @t@'s definition needs @x@ we have already walked past @x@'s binding site.
-------------------------------------------------------------------------------}

t2 :: Acc () [((Int, Int), Int)]
t2 = Generate () 4 "i" $
    EPair () (EPair () t t) x
  where
    x = ELit () (LInt 7)
    t = EMod () (EVar () "i") x

{-------------------------------------------------------------------------------
  t3: nested sharing

  @s@ is used twice /inside/ @n@, and @n@ is used twice. Both are genuinely
  shared. Also the term where the two /definitions/ tie on height and on size
  (both become a binary node over two leaves once their shared children are
  replaced by references) — so a proxy computed from the definition cannot order
  them; it has to come from the original subterm, or from the dependency directly.

  Expect: @s@ bound outside (or inside) @n@, @n@ bound at the inner pair; both
  present. Runs clean, @[((0,0),0),((1,1),0),((2,2),0),((3,3),0)]@.

  Fails as: nothing shared at all, if sharedness is "used by more than one
  distinct parent" (here both of @s@'s uses have the same parent, and so do both
  of @n@'s).
-------------------------------------------------------------------------------}

t3 :: Acc () [((Int, Int), Int)]
t3 = Generate () 4 "i" $
    EPair () (EPair () n n) (ELit () (LInt 0))
  where
    s = EMod () (EVar () "i") (ELit () (LInt 10))
    n = EUnlessZero () s s

{-------------------------------------------------------------------------------
  t4: over-marking becoming a strictness bug

  Only @p@ is shared: everything beneath it has exactly one use site. Counting
  /visits/ rather than /use sites/ marks @10 mod i@ (and its children) as shared
  too, which then gets its own binding /outside/ @p@'s — hoisting it past @p@'s
  guard, and under a strict 'ELet' that makes it unconditional.

  Expect: exactly one 'ELet', for @p@, with @10 mod i@ still inside it. Runs
  clean, @[((0,0),0),((0,0),0),((0,0),0),((1,1),0)]@.

  Fails as: divide by zero at @i == 0@.
-------------------------------------------------------------------------------}

t4 :: Acc () [((Int, Int), Int)]
t4 = Generate () 4 "i" $
    EPair () (EPair () p p) (ELit () (LInt 0))
  where
    p = EUnlessZero () (EVar () "i") (EMod () (ELit () (LInt 10)) (EVar () "i"))

{-------------------------------------------------------------------------------
  t5: shared under a guard *inside* a shared definition  [THE OPEN ONE]

  @s@ is genuinely shared (two use sites, both children of the inner
  'EUnlessZero'), and both of those use sites sit inside @p@'s body, under @p@'s
  guard. So @s@ belongs /inside/ @p@'s definition.

  Expect: @let p = unlessZero i (let s = 10 mod i in unlessZero s s) in (p, p)@.
  Runs clean, @[(0,0),(0,0),(0,0),(1,1)]@.

  Fails as: divide by zero at @i == 0@, because a flat definition scheme has
  nowhere to put @s@ except outside @p@'s binding, which hoists it past the guard.
-------------------------------------------------------------------------------}

t5 :: Acc () [(Int, Int)]
t5 = Generate () 4 "i" $
    EPair () p p
  where
    s = EMod () (ELit () (LInt 10)) (EVar () "i")
    p = EUnlessZero () (EVar () "i") (EUnlessZero () s s)

{-------------------------------------------------------------------------------
  t6: issue #116 itself

  The reference case. @10 mod i@ is shared across the two guarded branches, so its
  meet is /above both guards/; a strict 'ELet' there evaluates it unconditionally.

  Expect: exactly one 'ELet', above the 'EPair' — and then divide by zero at
  @i == 0@. The exception is the /point/: this is the bug being modelled.

  Fails as: more than one 'ELet' (dead bindings for unshared subterms).
-------------------------------------------------------------------------------}

t6 :: Acc () [(Int, Int)]
t6 = Generate () 4 "i" $
    EPair ()
      (EUnlessZero () (EVar () "i") x)
      (EUnlessZero () (EVar () "i") x)
  where
    x = EMod () (ELit () (LInt 10)) (EVar () "i")

{-------------------------------------------------------------------------------
  t7: the anti-over-hoisting guard

  @s@ is shared, but both uses sit under the /same/ guard, so its meet is under
  that guard and it must stay there. The mirror image of t6: here float-to-meet is
  safe, and hoisting any further is not.

  Expect: the 'ELet' for @s@ /inside/ the outer 'EUnlessZero'. Runs clean,
  @[(0,0),(0,0),(0,0),(1,0)]@.

  Fails as: divide by zero at @i == 0@ if the binding is lifted out of the guard.
-------------------------------------------------------------------------------}

t7 :: Acc () [(Int, Int)]
t7 = Generate () 4 "i" $
    EPair () (EUnlessZero () (EVar () "i") (EUnlessZero () s s)) (ELit () (LInt 0))
  where
    s = EMod () (ELit () (LInt 10)) (EVar () "i")

{-------------------------------------------------------------------------------
  t8: both uses under one parent

  The smallest term that needs (a) the child index in 'UseSite' — without it both
  edges collapse to one and @s@ reads as unshared — and (b) @needs@ to contain the
  node's own id, since the join point here is @s@'s own parent and /both/ its
  children are @s@.

  Expect: @let s = i mod 10 in unlessZero s s@, i.e. @[0,1,2,3]@.

  Fails as: no binding at all, or @s@ marked shared and never placed.
-------------------------------------------------------------------------------}

t8 :: Acc () [Int]
t8 = Generate () 4 "i" $
    EUnlessZero () s s
  where
    s = EMod () (EVar () "i") (ELit () (LInt 10))
