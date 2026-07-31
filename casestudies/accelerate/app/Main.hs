{-# OPTIONS_GHC -fno-cse #-} -- We do this manually, to illustrate the problem

module Main (main) where

import System.Environment

import MiniAccelerate

{-------------------------------------------------------------------------------
  Example from <https://github.com/AccelerateHS/accelerate-llvm/issues/116>
-------------------------------------------------------------------------------}

example116 :: Acc () [(Int, Int)]
example116 = Generate () 10 "i" $
    EPair ()
      (EUnlessZero () (EVar () "i") (EMod () (ELit () (LInt 10)) (EVar () "i")))
      (EUnlessZero () (EVar () "i") (EMod () (ELit () (LInt 10)) (EVar () "i")))

example116_cse :: Acc () [(Int, Int)]
example116_cse = Generate () 10 "i" $
    let x = EMod () (ELit () (LInt 10)) (EVar () "i") in
    EPair ()
      (EUnlessZero () (EVar () "i") x)
      (EUnlessZero () (EVar () "i") x)

{-------------------------------------------------------------------------------
  Main
-------------------------------------------------------------------------------}

run :: forall a. Show a => Acc () a -> IO ()
run example = do
    heapIds :: Acc HeapId a <- assignHeapIds example

    let useSites    :: UseSites = allUseSites heapIds
        shared      :: SubTerms = sharedSubTerms useSites $ allSubTerms heapIds
        sharingInfo :: Acc SharingInfo a = sharingAnalysis useSites heapIds
        withLets    :: Acc () a = insertLets shared sharingInfo

    putStrLn "== example"
    print example
    putStrLn "== assignHeapIds"
    print heapIds
    putStrLn "== allUseSites"
    print useSites
    putStrLn "== sharedSubTerms"
    print shared
    putStrLn "== sharingAnalysis"
    print sharingInfo
    putStrLn "== insertLets"
    print withLets
    putStrLn "== runAcc"
    print $ runAcc withLets

main :: IO ()
main = do
    args <- getArgs
    case args of
      ["run", "example116"]     -> run example116
      ["run", "example116_cse"] -> run example116_cse
      _otherwise -> putStrLn $ "Invalid args " ++ show args
