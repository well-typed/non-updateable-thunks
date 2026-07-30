-- | Mock/mini implementation of accelerate
--
-- Intentional deviations from accelerate:
--
-- * Most important simplifying assumption: we do NOT support nested sharing: we
--   assume that no shared term is a proper subterm of another shared term. If
--   this assumption is not met, 'insertLets' might either fail, reporting
--   unexpected leftover terms, or else produce a valid term which will however
--   duplicate work that you might have expected to be executed exactly once.
-- * We make no use of HOAS anywhere: the goal is to have representations
--   with 'Show' instances at every stage, so that we can use this more easily
--   as a vehicle for exploration.
-- * No de-Bruijn indices: user-chosen variables are simple strings, system
--   generated variables are just integers (identity, not index or level).
-- * We provide no type-level guard rails to ensure that variables are used
--   correctly; variable hygiene is left to the user (or to the code here).
-- * Algorithmic complexity is irrelevant: everything is aimed code clarity.
-- * The /specific/ way that we execute sharing analysis is different to what
--   happens in Accelerate, but the /concepts/ and the /overall approach/ is
--   the same.
-- * The AST is designed so that 'Exp' terms have at most /two/ children; this
--   makes some operations easier to define. Hence 'EUnlessZero', not 'EIf'.
-- * We try as much as possible to design the code to _explain_ the algorithm;
--   one way we do this is by using annotations on the terms themselves (@x@
--   type variable), so that it's easier to relate what is happening to
--   the term being processed.
-- * We currently only provide Let-binding for 'Exp', not 'Acc'. That's
--   sufficient to show the problem with issue #116, but it might be a
--   restriction we will want relax eventually.
module MiniAccelerate (
    -- * AST
    Literal(..)
  , Var(..)
  , Exp(..)
  , Acc(..)
    -- * Util
  , annExp
  , annAcc
  , mapAnnExp
  , mapAnnAcc
  , traverseAnnExp
  , traverseAnnAcc
    -- * Interpreter
  , runAcc
    -- * Introduce sharing
    -- ** Step 1: Inspect the heap
  , HeapId
  , assignHeapIds
    -- ** Step 2: Extract all subterms
  , SubTerms
  , allSubTerms
  , sharedSubTerms
    -- ** Step 3: Usage analysis
  , UseSite
  , UseSites
  , allUseSites
    -- ** Step 4: Sharing analysis
  , SharingInfo(..)
  , sharingAnalysis
    -- ** Step 5: Introduce lets
  , insertLets
  ) where

import Control.Monad.Identity
import Control.Monad.State
import Data.Function
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.String
import Data.Typeable
import GHC.Exts (Any)
import GHC.StableName
import Unsafe.Coerce

{-------------------------------------------------------------------------------
  AST
-------------------------------------------------------------------------------}

data Literal a where
  LInt :: Int -> Literal Int

data Var a =
    VarUsr String
  | VarSys HeapId
  deriving stock (Show, Eq)

instance IsString (Var a) where fromString = VarUsr

-- | Sequential computation
data Exp x a where
  ELit  :: x -> Literal a -> Exp x a
  EVar  :: x -> Var a -> Exp x a
  EPair :: x -> Exp x a -> Exp x b -> Exp x (a, b)
  ELet  :: x -> Var a -> Exp x a -> Exp x b -> Exp x b
  EMod  :: x -> Exp x Int -> Exp x Int -> Exp x Int

  -- | @EUnlessZero e1 e2 ~= if e1 == 0 then 0 else e2@
  EUnlessZero :: x -> Exp x Int -> Exp x Int -> Exp x Int

-- | Parallel computation
data Acc x a where
  Generate ::
      x
   -> Int        -- ^ Array size
   -> Var Int    -- ^ Variable to range over the array indices
   -> Exp x a    -- ^ Expression evaluating each array element
   -> Acc x [a]

deriving stock instance Show (Literal a)
deriving stock instance Show x => Show (Exp x a)
deriving stock instance Show x => Show (Acc x a)

{-------------------------------------------------------------------------------
  Annotations
-------------------------------------------------------------------------------}

annExp :: Exp x a -> x
annExp = \case
  ELit        x _     -> x
  EVar        x _     -> x
  EPair       x _ _   -> x
  ELet        x _ _ _ -> x
  EMod        x _ _   -> x
  EUnlessZero x _ _   -> x

annAcc :: Acc x a -> x
annAcc = \case
    Generate x _ _ _ -> x

traverseAnnExp :: forall f x y a.
     Applicative f
  => (x -> f y) -> Exp x a -> f (Exp y a)
traverseAnnExp f = go
  where
    go :: forall b. Exp x b -> f (Exp y b)
    go (ELit        x l)       = ELit        <$> f x <*> pure l
    go (EVar        x v)       = EVar        <$> f x <*> pure v
    go (EPair       x   e1 e2) = EPair       <$> f x            <*> go e1 <*> go e2
    go (ELet        x v e1 e2) = ELet        <$> f x <*> pure v <*> go e1 <*> go e2
    go (EMod        x   e1 e2) = EMod        <$> f x            <*> go e1 <*> go e2
    go (EUnlessZero x   e1 e2) = EUnlessZero <$> f x            <*> go e1 <*> go e2

traverseAnnAcc :: forall f x y a.
     Applicative f
  => (x -> f y) -> Acc x a -> f (Acc y a)
traverseAnnAcc f = go
  where
    go :: forall b. Acc x b -> f (Acc y b)
    go (Generate x n v e) = Generate <$> f x <*> pure n <*> pure v <*> traverseAnnExp f e

mapAnnExp :: (x -> y) -> Exp x a -> Exp y a
mapAnnExp f = runIdentity . traverseAnnExp (Identity . f)

mapAnnAcc :: (x -> y) -> Acc x a -> Acc y a
mapAnnAcc f = runIdentity . traverseAnnAcc (Identity . f)

foldAnnExp :: forall x y a. (x -> [y] -> y) -> Exp x a -> Exp y a
foldAnnExp f = go
  where
    go :: forall b. Exp x b -> Exp y b
    go (ELit        x l)       = ELit (f x []) l
    go (EVar        x v)       = EVar (f x []) v
    go (EPair       x   e1 e2) = binary EPair            x e1 e2
    go (ELet        x v e1 e2) = binary (\y -> ELet y v) x e1 e2
    go (EMod        x   e1 e2) = binary EMod             x e1 e2
    go (EUnlessZero x   e1 e2) = binary EUnlessZero      x e1 e2

    binary :: forall b c d.
         (y -> Exp y b -> Exp y c -> Exp y d)
      ->  x -> Exp x b -> Exp x c -> Exp y d
    binary constr x e1 e2 = constr (f x [annExp e1', annExp e2']) e1' e2'
      where
         e1' = go e1
         e2' = go e2

foldAnnAcc :: forall x y a. (x -> [y] -> y) -> Acc x a -> Acc y a
foldAnnAcc f = go
  where
    go :: forall b. Acc x b -> Acc y b
    go (Generate x n v e) = unary (\y -> Generate y n v) x e

    unary :: forall b c.
         (y -> Exp y b -> Acc y c)
      ->  x -> Exp x b -> Acc y c
    unary constr x e = constr (f x [annExp e']) e'
      where
         e' = foldAnnExp f e

{-------------------------------------------------------------------------------
  Interpreter
-------------------------------------------------------------------------------}

data Assign where
  Assign :: Var a -> !a -> Assign

type Env = [Assign]

sameVar :: forall a b. Var a -> Var b -> Maybe (a :~: b)
sameVar = unsafeCoerce aux
  where
    aux :: Var a -> Var a -> Maybe (a :~: a)
    aux v v' = if v == v' then Just Refl else Nothing

valueOf :: forall a. Var a -> Env -> a
valueOf v = go
  where
    go :: Env -> a
    go []                 = error $ "unbound " ++ show v
    go (Assign v' x:vars) =
        case sameVar v v' of
          Just Refl -> x
          Nothing   -> go vars

runLiteral :: Literal a -> a
runLiteral = \case
    LInt n -> n

runExp :: Env -> Exp x a -> a
runExp env = \case
    ELit        _ x       -> runLiteral x
    EVar        _ v       -> valueOf v env
    EPair       _   e1 e2 -> (runExp env e1, runExp env e2)
    ELet        _ x e1 e2 -> let !assign = Assign x $ runExp env e1
                             in runExp (assign : env) e2
    EMod        _   e1 e2 -> runExp env e1 `mod` runExp env e2
    EUnlessZero _   e1 e2 -> if runExp env e1 == 0 then 0 else runExp env e2

runAcc :: Acc x a -> a
runAcc = \case
    Generate _ sz i e ->
      [runExp [Assign i i'] e | i' <- [0 .. pred sz]]

{-------------------------------------------------------------------------------
  Step 1: inspect the heap
-------------------------------------------------------------------------------}

type HeapId = Int

getHeapId :: a -> StateT [(StableName Any, Int)] IO HeapId
getHeapId !x = do
    nm :: StableName Any <- liftIO $ unsafeCoerce <$> makeStableName x
    state $ \ids ->
      case lookup nm ids of
        Just i  -> (i, ids)
        Nothing -> let i = length ids in (i, (nm, i) : ids)

idsAcc :: Acc () a -> StateT [(StableName Any, Int)] IO (Acc HeapId a)
idsAcc a = do
    eid <- getHeapId a
    case a of
      Generate () n x e -> Generate eid n x <$> idsExp e

idsExp :: Exp () a -> StateT [(StableName Any, Int)] IO (Exp HeapId a)
idsExp e = do
    eid <- getHeapId e
    case e of
      ELit        () l       -> return $ ELit eid l
      EVar        () x       -> return $ EVar eid x
      EPair       ()   e1 e2 -> EPair       eid   <$> idsExp e1 <*> idsExp e2
      ELet        () x e1 e2 -> ELet        eid x <$> idsExp e1 <*> idsExp e2
      EMod        ()   e1 e2 -> EMod        eid   <$> idsExp e1 <*> idsExp e2
      EUnlessZero ()   e1 e2 -> EUnlessZero eid   <$> idsExp e1 <*> idsExp e2

assignHeapIds :: Acc () a -> IO (Acc HeapId a)
assignHeapIds = flip evalStateT [] . idsAcc

{-------------------------------------------------------------------------------
  Step 2: compute all subterms
-------------------------------------------------------------------------------}

data SubTerm x where
  SubExp :: Exp x a -> SubTerm x
  SubAcc :: Acc x a -> SubTerm x

deriving stock instance Show x => Show (SubTerm x)

type SubTerms = Map HeapId (SubTerm ())

subsExp :: Exp HeapId a -> State SubTerms ()
subsExp e = do
    modify $ Map.insert (annExp e) $ SubExp (mapAnnExp (const ()) e)
    case e of
      ELit        _ _        -> return ()
      EVar        _ _        -> return ()
      EPair       _    e1 e2 -> subsExp e1 >> subsExp e2
      ELet        _ _  e1 e2 -> subsExp e1 >> subsExp e2
      EMod        _    e1 e2 -> subsExp e1 >> subsExp e2
      EUnlessZero _    e1 e2 -> subsExp e1 >> subsExp e2

subsAcc :: Acc HeapId a -> State SubTerms ()
subsAcc a = do
    modify $ Map.insert (annAcc a) $ SubAcc (mapAnnAcc (const ()) a)
    case a of
      Generate _ _ _ e -> subsExp e

allSubTerms :: Acc HeapId a -> SubTerms
allSubTerms = flip execState Map.empty . subsAcc

letExp :: HeapId -> SubTerm () -> Exp () a -> Exp () a
letExp hid (SubExp e) = ELet () (VarSys hid) e
letExp _   (SubAcc _) = error "invalid subterm"

{-------------------------------------------------------------------------------
  Step 3: usage analysis
-------------------------------------------------------------------------------}

type UseSite  = (HeapId, Int) -- ^ the @i@th child of the given node
type UseSites = Map HeapId (Set UseSite)

allUseSites :: Acc HeapId a -> UseSites
allUseSites = snd . annAcc . foldAnnAcc aux
  where
    aux :: HeapId -> [(HeapId, UseSites)] -> (HeapId, UseSites)
    aux me kids = (
          me
        , Map.unionsWith Set.union $
              Map.fromListWith Set.union [
                  (kid, Set.singleton (me, i))
                | (kid, i) <- zip (map fst kids) [0..]
                ]
            : map snd kids
        )

isShared :: UseSites -> HeapId -> Bool
isShared useSites h = maybe False ((> 1) . Set.size) $ Map.lookup h useSites

sharedIds :: UseSites -> Set HeapId
sharedIds useSites = Set.filter (isShared useSites) (Map.keysSet useSites)

sharedSubTerms :: UseSites -> SubTerms -> SubTerms
sharedSubTerms useSites = flip Map.restrictKeys (sharedIds useSites)

{-------------------------------------------------------------------------------
  Step 4: Sharing analysis
-------------------------------------------------------------------------------}

data SharingInfo = SharingInfo{
      heapId :: HeapId

      -- | A node is shared if it has more than one use site
    , shared :: Bool

      -- | Free variables
      --
      -- For shared nodes, this will be the singleton 'heapId'
    , freeVars :: Set HeapId
    }
  deriving stock (Show)

sharingAnalysis :: UseSites -> Acc HeapId a -> Acc SharingInfo a
sharingAnalysis useSites a =
    foldAnnAcc aux a
  where
    aux :: HeapId -> [SharingInfo] -> SharingInfo
    aux me kids = SharingInfo{
          heapId   = me
        , shared
        , freeVars = if shared
                       then Set.singleton me
                       else Set.unions $ map (.freeVars) kids
        }
      where
        shared = isShared useSites me

{-------------------------------------------------------------------------------
  Insert Let bindings

  Let bindings are created at the /outer-most/ joint where a variable which is
  used more than once is used in /both/ branches.
-------------------------------------------------------------------------------}

isJoinPoint :: Exp x a -> Maybe (x, x)
isJoinPoint = \case
    ELit        _ _        -> Nothing
    EVar        _ _        -> Nothing
    EPair       _    e1 e2 -> Just (annExp e1, annExp e2)
    ELet        _ _  e1 e2 -> Just (annExp e1, annExp e2)
    EMod        _    e1 e2 -> Just (annExp e1, annExp e2)
    EUnlessZero _    e1 e2 -> Just (annExp e1, annExp e2)

inserts :: Exp SharingInfo a -> Set HeapId
inserts = maybe Set.empty (uncurry (Set.intersection `on` (.freeVars))) . isJoinPoint

-- 'State' is a bit strange for something that is scoped, but since every
-- variable is inserted exactly /once/, it's convenient
addLets :: forall term.
     (HeapId -> SubTerm () -> term -> term)
  -> Set HeapId -> State SubTerms (term -> term)
addLets f = \ids -> state $ \toInsert -> (
      aux (Map.toList $ Map.restrictKeys toInsert ids)
    , Map.withoutKeys toInsert ids
    )
  where
    aux :: [(HeapId, SubTerm ())] -> term -> term
    aux []               = id
    aux ((v, term):subs) = f v term . aux subs

letsExp :: Exp SharingInfo a -> State SubTerms (Exp () a)
letsExp e = do
    if (annExp e).shared
      then return $ EVar () (VarSys (annExp e).heapId)
      else do
        lets <- addLets letExp (inserts e)
        lets <$>
          case e of
            ELit        _ l       -> pure $ ELit () l
            EVar        _ v       -> pure $ EVar () v
            EPair       _   e1 e2 -> EPair       ()   <$> letsExp e1 <*> letsExp e2
            ELet        _ v e1 e2 -> ELet        () v <$> letsExp e1 <*> letsExp e2
            EMod        _   e1 e2 -> EMod        ()   <$> letsExp e1 <*> letsExp e2
            EUnlessZero _   e1 e2 -> EUnlessZero ()   <$> letsExp e1 <*> letsExp e2

letsAcc :: Acc SharingInfo a -> State SubTerms (Acc () a)
letsAcc a =
    case a of
      Generate _ n v e -> Generate () n v <$> letsExp e

insertLets :: SubTerms -> Acc SharingInfo a -> Acc () a
insertLets subterms = sanityCheck . flip runState subterms . letsAcc
  where
    sanityCheck :: (Acc () a, SubTerms) -> Acc () a
    sanityCheck (a, leftover) =
        if Map.null leftover
          then a
          else error "unexpected leftover terms"
