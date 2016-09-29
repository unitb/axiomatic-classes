{-# LANGUAGE TypeFamilies,RankNTypes,TupleSections
            ,FlexibleContexts,FlexibleInstances
            ,DeriveFunctor,DeriveFoldable
            ,ConstraintKinds,QuasiQuotes
            ,MultiParamTypeClasses
            ,UndecidableInstances
            ,DeriveGeneric
            ,TypeOperators
            ,DataKinds,ScopedTypeVariables
            ,DeriveTraversable,StandaloneDeriving #-}
module Data.Type.Map where

import Bound

import Control.Applicative
import Control.DeepSeq
import           Control.Lens hiding (Index,at,indices)
import qualified Control.Lens as L
import Control.Monad.State
import Control.Precondition

import           Data.Array as A hiding (indices,assocs,(!))
import qualified Data.Array as A 
import Data.Bifoldable
-- import Data.Bifunctor
import Data.Bitraversable
import Data.Bytes.Serial hiding (store)
import Data.Coerce
import Data.Constraint
import Data.DList as D
import Data.Foldable as F
import Data.Functor.Compose
import Data.List  as L hiding (partition)
import           Data.Map as M hiding (keys,partition,assocs,(!))
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid
import Data.Proxy
import Data.Proxy.TH
import Data.Reflection
import Data.Tuple
import Data.Type.Natural hiding ((:*:),(:+:))
import Data.Void

import GHC.Generics (Rep,Generic,M1(..),K1(..),(:*:)(..),(:+:)(..))
import GHC.Generics.Lens

import Test.QuickCheck
import Test.QuickCheck.ZoomEq

import Text.Pretty

import Unsafe.Coerce

import Utilities.Functor

newtype Subset k0 k1 = Subset (k0 -> k1)

flatten :: (Ord k,IsKey k) 
        => Table k a 
        -> (forall k'. IsKey k' => Subset k k' -> Table k' a -> r) 
        -> r
flatten t f = mkTable (M.keys . toMap $ t) $ \f' t' -> f (Subset $ fromJust . f') (at t <$> t')

keys :: IsKey k => Table k a -> [k]
keys _ = indices

values :: IsKey k => Table k a -> [a]
values = L.map snd . D.toList . toMap' id

assocs :: IsKey k => Table k a -> [(k,a)]
assocs = D.toList . ifoldMap (fmap D.singleton . (,))

reverseTable :: (IsKey vs,Ord n) => Table vs n -> Map n vs
reverseTable vs = M.fromList (swap <$> assocs vs)                             

mapKeys :: (IsKey k0,IsKey k1)
        => (k1 -> k0) 
        -> Table k0 a -> Table k1 a
mapKeys f t = store $ at t.f

newtype ReflKey a = ReflKey { getReflKey :: a }
    deriving (Eq,Ord,Functor,Foldable,Traversable)

class (Traversable (GTable k),Applicative (GTable k)) => GIsKey k where
    data GTable k :: * -> *
    gIndices :: [k p]
    gAt :: (k p) -> Lens' (GTable k a) a
    -- gDepth  :: GTable k a -> Int
    gToMap' :: (k p -> k') -> GTable k a -> DList (k',a)
    giTraverse :: Applicative f
               => (k p -> a -> f b)
               -> GTable k a
               -> f (GTable k b)
    gStore :: (k p -> a) -> GTable k a
    gIsEmpty :: Maybe (k p -> a)

at :: IsKey k => Table k a -> k -> a
at t x = t^.at' x

class (Traversable (Table k)
            ,TraversableWithIndex k (Table k)
            ,Ord k
            ,Applicative (Table k)) 
        => IsKey k where
    data Table k :: * -> *
    indices :: [k]
    at' :: k -> Lens' (Table k a) a
    toMap' :: (k -> k') -> Table k a -> DList (k',a)
    store :: (k -> a) -> Table k a
    isEmpty :: Maybe (k -> a)

instance IsKey Void where
    data Table Void a = VoidTable
        deriving (Functor,Foldable,Traversable)
    indices = []
    at' = absurd
    toMap' _ _ = D.empty
    store _ = VoidTable
    isEmpty = Just absurd

instance IsKey () where
    newtype Table () a = UnitTable a
        deriving (Functor,Foldable,Traversable)
    indices = [()]
    at' () = iso (\(UnitTable x) -> x) UnitTable
    toMap' f (UnitTable x) = D.singleton (f (),x)
    store f = UnitTable (f ())
    isEmpty = Nothing

-- newtype DecIndex k = DecIndex k
--     deriving (Ord,Eq)

-- instance Rewrapped (Table (DecIndex k) a) (Table (DecIndex k') a') where
-- instance Wrapped (Table (DecIndex k) a) where
--     type Unwrapped (Table (DecIndex k) a) = Table k a
--     _Wrapped' = iso unDecTable DecTable

instance Rewrapped (Table (Index n) a) (Table (Index n') a') where
instance Wrapped (Table (Index n) a) where
    type Unwrapped (Table (Index n) a) = Array (Index n) a
    _Wrapped' = iso getArrayTable IndexTable

instance Rewrapped (Table (ReflKey n) a) (Table (ReflKey n') a') where
instance Wrapped (Table (ReflKey n) a) where
    type Unwrapped (Table (ReflKey n) a) = GTable (Rep n) a
    _Wrapped' = iso unReflTable ReflTable

instance Rewrapped (Table (x,y) a) (Table (x',y') a') where
instance Wrapped (Table (x,y) a) where
    type Unwrapped (Table (x,y) a) = Table x (Table y a)
    _Wrapped' = iso unPairTable PairTable

instance Rewrapped (GTable (M1 a b c) z) (GTable (M1 a' b' c') z') where
instance Wrapped (GTable (M1 a b c) z) where
    type Unwrapped (GTable (M1 a b c) z) = GTable c z
    _Wrapped' = iso unM1Table M1Table

instance Rewrapped (GTable (K1 a b) z) (GTable (K1 a' b') z') where
instance Wrapped (GTable (K1 a b) z) where
    type Unwrapped (GTable (K1 a b) z) = Table b z
    _Wrapped' = iso unK1Table K1Table

instance Rewrapped (GTable (a :*: b) z) (GTable (a' :*: b') z') where
instance Wrapped (GTable (a :*: b) z) where
    type Unwrapped (GTable (a :*: b) z) = GTable a (GTable b z)
    _Wrapped' = iso unTimesTable TimesTable

type instance IxValue (Table k a) = a
type instance L.Index (Table k a) = k

instance IsKey k => Ixed (Table k a) where
    ix = at'

-- instance IsKey k => IsKey (DecIndex k) where
--     newtype Table (DecIndex k) a = DecTable { unDecTable :: Table k a }
--     at' (DecIndex i) = _Wrapped.at' i
--     indices = DecIndex <$> indices
--     toMap' f (DecTable t) = toMap' (f . DecIndex) t
--     store = DecTable . store . lmap DecIndex
--     isEmpty = lmap DecIndex <$> isEmpty

instance IsKey k => IsKey (RIndex s k) where
    newtype Table (RIndex s k) a = ReifTable (Table k a)
    at' (RIndex i) = _Wrapped.at' i
    indices = RIndex <$> indices
    toMap' f (ReifTable t) = toMap' (f . RIndex) t
    store = ReifTable . store . lmap RIndex
    isEmpty = lmap getRIndex <$> isEmpty

isEmptySing :: SNat n -> Maybe (Index n -> a)
isEmptySing n | sNatToInt n == 0 = Just undefined'
              | otherwise        = Nothing

instance SingI n => IsKey (Index n) where
    newtype Table (Index n) a = IndexTable { getArrayTable :: Array (Index n) a }
        deriving (Functor,Foldable,Traversable)
    at' i = _Wrapped . lens (A.! i) (\a x -> a // [(i,x)])
    indices = [ Index i | i <- [1 .. sNatToInt (sing :: SNat n)] ]
    toMap' f (IndexTable ar) = D.fromList [ (f i,x) | (i,x) <- A.assocs ar ]
    store = IndexTable . mkArray
    isEmpty = isEmptySing sing

instance (Ord k,Bounded k,Generic k,GIsKey (Rep k)) => IsKey (ReflKey k) where
    newtype Table (ReflKey k) a = ReflTable { unReflTable :: GTable (Rep k) a }
    indices = gIndices & mapped %~ ReflKey . view (from generic)
    at' (ReflKey i) = _Wrapped.gAt (i^.generic)
    toMap' f (ReflTable t) = gToMap' (f.ReflKey . view (from generic)) t
    store = ReflTable . gStore . (. ReflKey . view (from generic))
    isEmpty = lmap (view generic . getReflKey) <$> gIsEmpty

instance (IsKey t0,IsKey t1) => IsKey (t0,t1) where
    newtype Table (t0,t1) a = PairTable { unPairTable :: Table t0 (Table t1 a) }
    at' (x,y) = _Wrapped.at' x.at' y
    indices = [ (i,j) | i <- indices, j <- indices ]
    toMap' f (PairTable t) = F.fold $ imap (toMap' . curry f) t
    store = PairTable . store . fmap store . curry
    isEmpty = ((\f -> f . fst) <$> isEmpty) <|> ((\f -> f . snd) <$> isEmpty)

instance (IsKey t0,IsKey t1) => IsKey (Either t0 t1) where
    data Table (Either t0 t1) a = EitherTable { leftTable :: Table t0 a, rightTable :: Table t1 a }
    at' (Left k)  f (EitherTable m0 m1) = (\m0' -> EitherTable m0' m1) <$> at' k f m0
    at' (Right k) f (EitherTable m0 m1) = (\m1' -> EitherTable m0 m1') <$> at' k f m1
    indices = (Left <$> indices) ++ (Right <$> indices)
    toMap' f (EitherTable m0 m1)   = toMap' (f.Left) m0 <> toMap' (f.Right) m1
    store f = EitherTable (store $ f.Left) (store $ f.Right)
    isEmpty = liftA2 either isEmpty isEmpty

toMap :: (Ord k,IsKey k) => Table k a -> Map k a
toMap = M.fromList . D.toList . toMap' id

deriving instance (IsKey k) => Functor (Table (RIndex s k))
deriving instance (IsKey k) => Foldable (Table (RIndex s k))
deriving instance (IsKey k) => Traversable (Table (RIndex s k))
-- deriving instance (IsKey k) => Functor (Table (DecIndex k))
-- deriving instance (IsKey k) => Foldable (Table (DecIndex k))
-- deriving instance (IsKey k) => Traversable (Table (DecIndex k))
deriving instance (IsKey t0,IsKey t1) => Functor (Table (Either t0 t1))
deriving instance (IsKey t0,IsKey t1) => Foldable (Table (Either t0 t1))
deriving instance (IsKey t0,IsKey t1) => Traversable (Table (Either t0 t1))
deriving instance (IsKey t0,IsKey t1) => Functor (Table (t0,t1))
deriving instance (IsKey t0,IsKey t1) => Foldable (Table (t0,t1))
deriving instance (IsKey t0,IsKey t1) => Traversable (Table (t0,t1))
deriving instance (GIsKey (Rep k)) => Functor (Table (ReflKey k))
deriving instance (GIsKey (Rep k)) => Foldable (Table (ReflKey k))
deriving instance (GIsKey (Rep k)) => Traversable (Table (ReflKey k))
deriving instance (GIsKey k) => Functor (GTable (M1 a b k))
deriving instance (GIsKey k) => Foldable (GTable (M1 a b k))
deriving instance (GIsKey k) => Traversable (GTable (M1 a b k))
deriving instance (IsKey k) => Functor (GTable (K1 a k))
deriving instance (IsKey k) => Foldable (GTable (K1 a k))
deriving instance (IsKey k) => Traversable (GTable (K1 a k))
deriving instance (GIsKey a,GIsKey b) => Functor (GTable (a :+: b))
deriving instance (GIsKey a,GIsKey b) => Foldable (GTable (a :+: b))
deriving instance (GIsKey a,GIsKey b) => Traversable (GTable (a :+: b))
deriving instance (GIsKey a,GIsKey b) => Functor (GTable (a :*: b))
deriving instance (GIsKey a,GIsKey b) => Foldable (GTable (a :*: b))
deriving instance (GIsKey a,GIsKey b) => Traversable (GTable (a :*: b))

instance FunctorWithIndex Void (Table Void) where
instance FoldableWithIndex Void (Table Void) where
instance TraversableWithIndex Void (Table Void) where
    itraverse _ VoidTable = pure VoidTable
instance FunctorWithIndex () (Table ()) where
instance FoldableWithIndex () (Table ()) where
instance TraversableWithIndex () (Table ()) where
    itraverse f (UnitTable x) = UnitTable <$> f () x
instance FunctorWithIndex (Index n) (Table (Index n)) where
instance FoldableWithIndex (Index n) (Table (Index n)) where
instance TraversableWithIndex (Index n) (Table (Index n)) where
    itraverse f (IndexTable ar) = IndexTable <$> itraverse f ar
instance IsKey n => FunctorWithIndex (RIndex s n) (Table (RIndex s n)) where
instance IsKey n => FoldableWithIndex (RIndex s n) (Table (RIndex s n)) where
instance IsKey n => TraversableWithIndex (RIndex s n) (Table (RIndex s n)) where
    itraverse f (ReifTable ar) = ReifTable <$> itraverse (f . RIndex) ar
-- instance IsKey n => FunctorWithIndex (DecIndex n) (Table (DecIndex n)) where
-- instance IsKey n => FoldableWithIndex (DecIndex n) (Table (DecIndex n)) where
-- instance IsKey n => TraversableWithIndex (DecIndex n) (Table (DecIndex n)) where
--     itraverse f (DecTable ar) = DecTable <$> itraverse (f . DecIndex) ar
instance (IsKey a,IsKey b) => FunctorWithIndex (Either a b) (Table (Either a b)) where
instance (IsKey a,IsKey b) => FoldableWithIndex (Either a b) (Table (Either a b)) where
instance (IsKey a,IsKey b) => TraversableWithIndex (Either a b) (Table (Either a b)) where
    itraverse f (EitherTable m0 m1) = EitherTable
            <$> itraverse (f.Left) m0
            <*> itraverse (f.Right) m1
instance (IsKey a,IsKey b) => FunctorWithIndex (a,b) (Table (a,b)) where
instance (IsKey a,IsKey b) => FoldableWithIndex (a,b) (Table (a,b)) where
instance (IsKey a,IsKey b) => TraversableWithIndex (a,b) (Table (a,b)) where
    itraverse f (PairTable t) = PairTable
            <$> itraverse (itraverse . curry f) t
instance (Generic k,GIsKey (Rep k)) => FunctorWithIndex (ReflKey k) (Table (ReflKey k)) where
instance (Generic k,GIsKey (Rep k)) => FoldableWithIndex (ReflKey k) (Table (ReflKey k)) where
instance (Generic k,GIsKey (Rep k)) => TraversableWithIndex (ReflKey k) (Table (ReflKey k)) where
    itraverse f (ReflTable t) = ReflTable <$> giTraverse (f . ReflKey . view (from generic)) t

-- instance Applicative (Table Void) where
--     pure _ = VoidTable
--     VoidTable <*> VoidTable = VoidTable
-- instance Applicative (Table ()) where
--     pure = UnitTable
--     UnitTable f <*> UnitTable x = UnitTable (f x)
-- instance SingI n => Applicative (Table (Index n)) where
--     pure x = IndexTable $ mkArray (const x)
--     IndexTable f <*> IndexTable x = IndexTable $ mkArray $ \i -> (f A.! i) (x A.! i)
-- instance (IsKey a,IsKey b) => Applicative (Table (Either a b)) where
--     pure x = EitherTable (pure x) (pure x)
--     EitherTable f0 f1 <*> EitherTable x0 x1 = EitherTable (f0 <*> x0) (f1 <*> x1)
-- instance (GIsKey (Rep k)) => Applicative (Table (ReflKey k)) where
--     pure = ReflTable . pure
--     ReflTable f <*> ReflTable x = ReflTable $ f <*> x
--     -- PairTable f <*> PairTable x = PairTable $ liftA2 (<*>) f x
-- instance (IsKey a,IsKey b) => Applicative (Table (a,b)) where
--     pure x = PairTable $ pure (pure x)
--     PairTable f <*> PairTable x = PairTable $ liftA2 (<*>) f x
-- -- instance (IsKey a,IsKey b) => Applicative (Table (a,b,c)) where
-- --     pure x = TripleTable $ pure x
-- --     PairTable f <*> PairTable x = TripleTable $ (<*>) f x
instance (IsKey k) => Applicative (Table k) where
    pure = store . const
    f <*> x = store $ at f <*> at x

instance (GIsKey k) => Applicative (GTable k) where
    pure = gStore . const
    f <*> x = gStore $ \i -> (f^.gAt i) (x^.gAt i)
-- instance (GIsKey c) => Applicative (GTable (M1 a b c)) where
--     pure = M1Table . pure
--     M1Table f <*> M1Table x = M1Table $ f <*> x
-- instance (GIsKey a,GIsKey b) => Applicative (GTable (a :*: b)) where
--     pure = TimesTable . pure . pure
--     TimesTable f <*> TimesTable x = TimesTable $ liftA2 (<*>) f x
-- instance (GIsKey a,GIsKey b) => Applicative (GTable (a :+: b)) where
--     pure x = PlusTable (pure x) (pure x)
--     PlusTable f0 f1 <*> PlusTable x0 x1 = PlusTable (f0 <*> x0) (f1 <*> x1)
-- instance (IsKey b) => Applicative (GTable (K1 a b)) where
--     pure = K1Table . pure
--     K1Table f <*> K1Table x = K1Table $ f <*> x

instance GIsKey c => GIsKey (M1 a b c) where
    newtype GTable (M1 a b c) z = M1Table { unM1Table :: GTable c z }
    gIndices = M1 <$> gIndices
    gAt (M1 k) = _Wrapped.gAt k
    giTraverse f (M1Table t) = M1Table <$> giTraverse (f.M1) t
    gToMap' f (M1Table t) = gToMap' (f.M1) t
    gStore f = M1Table $ gStore (f.M1)
    gIsEmpty = lmap unM1 <$> gIsEmpty
instance (GIsKey a,GIsKey b) => GIsKey (a :*: b) where
    newtype GTable (a :*: b) z = TimesTable { unTimesTable :: GTable a (GTable b z) }
    gIndices = [ i :*: j | i <- gIndices, j <- gIndices ]
    gAt (i :*: j) = _Wrapped.gAt i.gAt j
    giTraverse f (TimesTable t) = TimesTable <$> giTraverse (giTraverse . curry' f) t
    gToMap' f (TimesTable t) = F.fold $ giMap (gToMap' . curry' f) t
    gStore f = TimesTable $ gStore $ gStore . curry' f
    gIsEmpty = ((\f (x :*: _) -> f x) <$> gIsEmpty) <|> ((\f (_ :*: x) -> f x) <$> gIsEmpty)

giMap :: GIsKey k 
      => (k p -> a -> b) 
      -> GTable k a 
      -> GTable k b
giMap f = runIdentity . giTraverse (fmap Identity . f)

curry' :: ((a :*: b) p -> t) -> a p -> b p -> t
curry' f x y = f (x :*: y)

plus :: (a p -> r) 
     -> (b p -> r) 
     -> (a :+: b) p 
     -> r
plus f _g (L1 x) = f x
plus _f g (R1 x) = g x

instance (GIsKey a,GIsKey b) => GIsKey (a :+: b) where
    data GTable (a :+: b) z = PlusTable (GTable a z) (GTable b z)
    gIndices = (L1 <$> gIndices) ++ (R1 <$> gIndices)
    gAt (L1 i) f (PlusTable t0 t1) = (\t0' -> PlusTable t0' t1) <$> gAt i f t0
    gAt (R1 i) f (PlusTable t0 t1) = (\t1' -> PlusTable t0 t1') <$> gAt i f t1
    giTraverse f (PlusTable t0 t1) = PlusTable
            <$> giTraverse (f.L1) t0
            <*> giTraverse (f.R1) t1
    gToMap' f (PlusTable t0 t1) = gToMap' (f.L1) t0 <> gToMap' (f.R1) t1
    gStore f = PlusTable (gStore $ f.L1) (gStore $ f.R1)
    gIsEmpty = liftA2 plus gIsEmpty gIsEmpty
instance IsKey b => GIsKey (K1 a b) where
    newtype GTable (K1 a b) z = K1Table { unK1Table :: Table b z }
    gIndices = K1 <$> indices
    gAt (K1 k) = _Wrapped.at' k
    giTraverse f (K1Table t) = K1Table <$> itraverse (f.K1) t
    gToMap' f (K1Table t) = toMap' (f.K1) t
    gStore f = K1Table $ store (f.K1)
    gIsEmpty = lmap unK1 <$> isEmpty

newtype Index (n :: Nat) = Index { getIndex :: Int }
    deriving (Eq,Ord,Ix)

upper :: SNat n -> Index n
upper = Index . sNatToInt

mkArray :: SingI n => (Index n -> a) -> Array (Index n) a
mkArray f = array rng [ (i,f i) | i <- range rng ]
    where
        rng = (Index 1,upper sing)

toIntMap :: Traversable t => t a -> t (Int, a)
toIntMap t = evalState (traverse next t) (0 :: Int)
    where
        next x = get >>= \n -> modify succ >> return (n,x)

data Reflected s

unsafeFMapCoerce :: (Functor t,Functor t'
                    ,Coercible a b,Coercible a' b') 
                 => Iso (t a) (t' a') (t b) (t' b')
unsafeFMapCoerce = iso unsafeCoerce unsafeCoerce `sameTypeAs` mapping coerced

unsafeBimapCoerce :: (Bifunctor t
                     ,Bifunctor t'
                     ,Coercible a a'
                     ,Coercible b b'
                     ,Coercible c c'
                     ,Coercible d d') 
                  => Iso (t a b) (t' c d) (t a' b') (t' c' d')
unsafeBimapCoerce = iso unsafeCoerce unsafeCoerce `sameTypeAs` bimapping coerced coerced

sameTypeAs :: a -> a -> a
sameTypeAs x _ = x

newtype RIndex s k = RIndex { getRIndex :: k }
    deriving (Eq,Ord,Functor,Foldable,Traversable,Generic)

instance NFData k => NFData (RIndex s k) where

instance Serial k => Serial (RIndex s k) where

instance (IsKey k,Reifies s (Table k a),PrettyPrintable a) 
        => PrettyPrintable (RIndex (Reflected s) k) where
    pretty k@(RIndex x) = pretty $ at (reflect $ Compose $ Swap1 k) x

instance (IsKey k,Reifies s (Table k a),Show a) => Show (RIndex (Reflected s) k) where
    show k@(RIndex x) = show $ at (reflect $ Compose $ Swap1 k) x

instance Arbitrary k => Arbitrary (RIndex s k) where
    arbitrary = RIndex <$> arbitrary
    shrink = genericShrink

instance Bifunctor RIndex where
    bimap _ f (RIndex x) = RIndex $ f x
instance Bifoldable RIndex where
    bifoldMap _ f (RIndex x) = f x
instance Bitraversable RIndex where
    bitraverse _ f (RIndex x) = RIndex <$> f x
instance Profunctor RIndex where
    dimap _ f (RIndex x) = RIndex $ f x

instance (ZoomEq k,Show (RIndex s k)) => ZoomEq (RIndex s k) where

instance Rewrapped (RIndex s k) (RIndex s' k') where
instance Wrapped (RIndex s k) where
    type Unwrapped (RIndex s k) = k
    _Wrapped' = iso getRIndex RIndex

instance Rewrapped (Table (RIndex s k) a) (Table (RIndex s' k') a') where
instance Wrapped (Table (RIndex s k) a) where
    type Unwrapped (Table (RIndex s k) a) = Table k a
    _Wrapped' = iso (\(ReifTable t) -> t) ReifTable

class IsKey k => HasValue a k | k -> a where
    value :: k -> a
instance (IsKey k,Reifies s (Table k a)) => HasValue a (RIndex (Reflected s) k) where
    value x@(RIndex k) = at (reflect $ Compose $ Swap1 x) k

toArrayMapping :: IsKey k 
               => Table k a 
               -> (Table k Int, Array Int a)
toArrayMapping t = (t', array (1,length xs) xs)
    where
        t' = serialNumber t
        xs = F.toList $ liftA2 (,) t' t

serialNumber :: IsKey k => Table k a -> Table k Int
serialNumber t = evalState (traverse (const next) t) 0
    where
        next = modify succ >> get

mkTableWith :: forall a r. Ord a
            => [a] 
            -> (forall k. HasValue a k => (a -> Maybe k) -> Table k a -> r)
            -> r
mkTableWith xs f = mkTable' [pr|IsKey|] Dict Dict Dict xs (fmap const <$> f)

mkTable :: forall a r. Ord a
        => [a] 
        -> (forall k. HasValue a k => (a -> Maybe k) -> Table k a -> r)
        -> r
mkTable xs f = mkTable' [pr|IsKey|] Dict Dict Dict xs (fmap const <$> f)

mkTable' :: forall a c r. Ord a
         => Proxy c
         -> Dict (c Void)
         -> Dict (c ())
         -> (forall n. SingI n => Dict (c (Index n)))
         -> [a] 
         -> (forall k s. (c k,Reifies s (Table k a)) 
                => (a -> Maybe (RIndex (Reflected s) k)) 
                -> Table (RIndex (Reflected s) k) a 
                -> Proxy s 
                -> r)
         -> r
mkTable' _ Dict _ _ [] f    = reify VoidTable $ f (const Nothing)  (ReifTable VoidTable)
mkTable' _ _ Dict _ [x] f   = reify (UnitTable x) $ f (\y -> guard (x == y) >> Just (RIndex ())) (ReifTable $ UnitTable x)
mkTable' _ _ _ d xs f    = withNum (M.size m) $ f' d (`M.lookup` m)   (IndexTable ar)
    where
        f' :: SingI n
           => Dict (c (Index n))
           -> (a -> Maybe (Index n))
           -> Table (Index n) a
           -> SNat n 
           -> r
        f' Dict m' t' _ = reify t' $ f (pure . RIndex <=< m') (ReifTable t')
        m :: forall n. Map a (Index n)
        m = evalState (M.fromList ((,()) <$> xs) & traverse num) 1
        num _ = get >>= \x -> modify succ >> return (Index x)
        ar :: forall n. Array (Index n) a
        ar = array (Index 1,Index $ M.size m) $ swap <$> M.toList m

withNum :: Int -> (forall n. SingI n => SNat n -> r) -> r
withNum n f = withSomeSing (intToNat n) $ \n' -> withSingI n' (f n')
-- withNum n f = withSingI (f n)
-- withNum n f | n <= 0 = f sZero
            -- | otherwise = withNum (n-1) _

-- firstEntry :: IsKey k => Table k a -> Maybe k
-- firstEntry _ = indices

null :: IsKey k => Table k a -> Bool 
null = L.null . keys

ifSubset :: (Ord a,IsKey k1,IsKey k0)
         => Table k0 a 
         -> Table k1 a
         -> ([a] -> r)
         -> (   (k0 -> k1) 
             -> (k1 -> Maybe k0) 
             -> r)
         -> r
ifSubset t0 t1 r f 
        | (() <$ m0) `isSubmapOf` (() <$ m1) 
                    = f ((m1 !) <$> at t0) ((`M.lookup` m0) <$> at t1)
        | otherwise = r xs
    where
        m0 = reverseTable t0
        m1 = reverseTable t1
        xs = M.keys $ m0 `difference` m1

ifEqual :: (Ord a,IsKey k1,IsKey k0)
        => Table k0 a 
        -> Table k1 a
        -> r
        -> (forall k. (IsKey k)
             => (k0 -> k)
             -> (k1 -> k)
             -> Table k a
             -> r)
        -> r
ifEqual t0 t1 r f 
    | isEqual =             mkTable [1..M.size mm]
                $ \fM tM -> f 
                        (\x -> fromJust $ fM $ mL M.! x)
                        (\x -> fromJust $ fM $ mR M.! x)
                        -- (at t0 <$> tL) 
                        ((ar A.!) <$> tM) 
                        -- (at t1 <$> tR)
    | otherwise = r
    where
        isEqual = M.size mm == M.size mL && M.size mm == M.size mR
        mm = M.intersectionWith (,) m0 m1
        mL = M.fromList $ zip (fst <$> M.elems mm) [1..]
        mR = M.fromList $ zip (snd <$> M.elems mm) [1..]
        ar = listArray (1,M.size mm) (M.keys mm)
        m0 = swap' $ toMap t0
        m1 = swap' $ toMap t1

partition' :: (Ord a,IsKey k1,IsKey k0)
           => Table k0 a -> Table k1 a
           -> (forall kl kc kr. (IsKey kl,IsKey kc,IsKey kr)
                => (k0 -> Var kl kc)
                -> (k1 -> Var kr kc)
                -> Table kl a
                -> Table kc a
                -> Table kr a
                -> r)
           -> r
partition' t0 t1 f = partition t0 t1 $ \g h -> f (either B F . g) (either B F . h)

partition :: (Ord a,IsKey k1,IsKey k0)
          => Table k0 a -> Table k1 a
          -> (forall kl kc kr. (IsKey kl,IsKey kc,IsKey kr)
                => (k0 -> Either kl kc)
                -> (k1 -> Either kr kc)
                -> Table kl a
                -> Table kc a
                -> Table kr a
                -> r)
          -> r
partition t0 t1 f =         mkTable (M.elems $ m0 `M.difference` m1)
                $ \fL tL -> mkTable [1..M.size mm]
                $ \fM tM -> mkTable (M.elems $ m1 `M.difference` m0)
                $ \fR tR -> f 
                        (\x -> fromJust $ (Left <$> fL x) <|> (Right <$> fM (mL M.! x)))
                        (\x -> fromJust $ (Left <$> fR x) <|> (Right <$> fM (mR M.! x)))
                        (at t0 <$> tL) 
                        ((ar A.!) <$> tM) 
                        (at t1 <$> tR)
    where
        mm = M.intersectionWith (,) m0 m1
        mL = M.fromList $ zip (fst <$> M.elems mm) [1..]
        mR = M.fromList $ zip (snd <$> M.elems mm) [1..]
        ar = listArray (1,M.size mm) (M.keys mm)
        m0 = swap' $ toMap t0
        m1 = swap' $ toMap t1

swap' :: Ord a => Map k a -> Map a k
swap' = M.fromList . L.map swap . M.toList

merge :: Table k0 a -> Table k1 a -> Table (Either k0 k1) a
merge = EitherTable

takeLeft :: Table (Either k0 k1) a -> Table k0 a
takeLeft (EitherTable m _) = m

takeRight :: Table (Either k0 k1) a -> Table k1 a
takeRight (EitherTable _ m) = m

instance (IsKey v,Eq a) => Eq (Table v a) where
    x == y = F.and $ (==) <$> x <*> y

instance (IsKey v,Ord a) => Ord (Table v a) where
    compare x y = F.fold $ compare <$> x <*> y

data MyKey k0 k1 = One k0 | Two k0 k0 | Three k0 k0 k1
    deriving (Generic)

rewriteMyKey :: (IsKey k0,IsKey k1)
             => (k0 -> a -> b)
             -> Table (ReflKey (MyKey k0 k1)) a
             -> Table (ReflKey (MyKey k0 k1)) b
rewriteMyKey f = imap f'
    where
        f' (ReflKey (One x)) = f x
        f' (ReflKey (Two x _)) = f x
        f' (ReflKey (Three x _ _)) = f x

main :: IO ()
main = print $ mkTable ([1..4] :: [Int]) (\f m -> [6,5..0] & traverse %~ fmap (at m).f)
