{-# LANGUAGE DeriveGeneric
    ,TypeFamilies
    ,StandaloneDeriving
    ,UndecidableInstances
    ,RankNTypes
    ,ExistentialQuantification
    ,FlexibleInstances
    ,MultiParamTypeClasses
    ,FunctionalDependencies #-}
module Data.Packaged where

import Control.DeepSeq
import Control.Lens
import Control.Monad
import Control.Monad.Loops

import Data.ByteString hiding (putStrLn)
import Data.Bytes.Get as Ser
import Data.Binary
import Data.Bytes.Put as Ser
import Data.Bytes.Serial as Ser
import Data.Char
import Data.Data
import Data.Either.Combinators
import Data.Functor.Classes
import Data.Hashable
import Data.List.NonEmpty
import Data.Semigroup
import Data.String

import GHC.Generics.Instances

import Language.Haskell.TH.Syntax

import Test.QuickCheck

newtype Packaged a = Package { getPackage :: ByteString }
    deriving (Eq,Ord,Data,Generic,Hashable)

packaged :: (Serial a,Serial b)
         => Iso a b (Packaged a) (Packaged b)
packaged = iso (Package . runPutS . serialize) (fromRight' . runGetS deserialize . getPackage)

unpackaged :: (Serial a,Serial b)
           => Iso (Packaged a) (Packaged b) a b
unpackaged = from packaged

instance Serial a => Wrapped (Packaged a) where
    type Unwrapped (Packaged a) = a
    _Wrapped' = unpackaged

instance Serial (Packaged a) where

class OnPackaged a where
    type UnpackedFun a :: *
    onPackaged :: UnpackedFun a -> a

instance (Serial a,OnPackaged b) => OnPackaged (Packaged a -> b) where
    type UnpackedFun (Packaged a -> b) = a -> UnpackedFun b
    onPackaged f x = onPackaged $ f $ x^.unpackaged

instance Serial a => OnPackaged (Packaged a) where
    type UnpackedFun (Packaged a) = a
    onPackaged = view packaged

instance (Serial a,Show a) => Show (Packaged a) where
    show = show . view unpackaged

instance NFData (Packaged a) where

newtype NullTerminated f = NullTerm {getNullString :: f Char}
    deriving (Typeable,Generic)
type NullTerminatedString = NullTerminated []
type NullTerminatedNEString = NullTerminated NonEmpty

deriving instance (Typeable f,Data (f Char)) => Data (NullTerminated f)

instance Eq1 f => Eq (NullTerminated f) where
    NullTerm x == NullTerm y = eq1 x y
instance Ord1 f => Ord (NullTerminated f) where
    NullTerm x `compare` NullTerm y = compare1 x y

instance Show (NullTerminated []) where
    show = show . getNullString
instance Show (NullTerminated NonEmpty) where
    show = show . getNullString

instance IsString NullTerminatedString where
    fromString = NullTerm

instance NFData1 f => NFData (NullTerminated f) where
    rnf = rnf1 . getNullString

instance Wrapped (NullTerminated f) where
    type Unwrapped (NullTerminated f) = f Char
    _Wrapped' = iso getNullString NullTerm

instance Serial (NullTerminated []) where
    serialize (NullTerm xs) = mapM_ serialize xs >> serialize (chr 0)
    {-# INLINE deserialize #-}
    deserialize = NullTerm <$> 
            whileJust (do x <- deserialize ; return (if x == chr 0 then Nothing else Just x)) return

putNullTerminated :: Foldable t => t Char -> Put
putNullTerminated xs = mapM_ serialize xs >> serialize (chr 0)

getNullTerminatedList :: Get String
getNullTerminatedList = do
        x <- get
        if x == chr 0 
            then return []
            else (x:) <$> getNullTerminatedList

getNullTerminatedNEList :: Get (NonEmpty Char)
getNullTerminatedNEList = maybe mzero return . nonEmpty =<< getNullTerminatedList

instance Serial (NullTerminated NonEmpty) where
    serialize (NullTerm xs) = mapM_ serialize xs >> serialize (chr 0)
    {-# INLINE deserialize #-}
    deserialize = fmap NullTerm $
        liftM2 (:|) deserialize
             $ whileJust (do x <- deserialize ; return (if x == chr 0 then Nothing else Just x)) return

instance Hashable NullTerminatedNEString where
instance Hashable NullTerminatedString where

instance Semigroup NullTerminatedNEString where
    (<>) = genericSemigroupMAppend
instance Semigroup NullTerminatedString where
instance Monoid NullTerminatedString where
    mappend = genericMAppend
    mempty = genericMEmpty
    mconcat = genericMConcat

instance Lift1 f => Lift (NullTerminated f) where
    lift x = [e| NullTerm $(lift1 $ getNullString x) |]

instance (Arbitrary a,Serial a) => Arbitrary (Packaged a) where
    arbitrary = arbitrary & mapped %~ view packaged
    shrink = unpackaged shrink
