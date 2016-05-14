
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,DeriveAnyClass #-}
-- {-# LANGUAGE StandaloneDeriving #-}
-- {-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE KindSignatures #-}
-- {-# LANGUAGE DeriveGeneric #-}
--{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies, TypeOperators, KindSignatures, PolyKinds #-}
{-# LANGUAGE DataKinds, GADTs #-}
--{-# LANGUAGE TypeFamilyDependencies #-}


module Data.HMap.Internal({-Reverse-}Merge, Sort) where

import GHC.TypeLits
import Data.Proxy

--type family ReverseTC (a :: [ k ]) (res :: [ k ] )   :: ( [k])    where
--    ReverseTC '[] res = res
--    ReverseTC (a ': bs ) res = ReverseTC bs (a ':  res)

--type family Reverse  (a :: [k]) =  (result  :: [k])    where
--  Reverse a = ReverseTC a '[]


--type family MergeTC (x :: [(Symbol,k)]) (y :: [(Symbol,k)])  (res :: [(Symbol,k)]) :: [(Symbol,k) ] where
--  MergeTC '[] '[] res = Reverse res
--  MergeTC (a ': as) '[] res = MergeTC as '[] (a ': res)
--  MergeTC '[] bs res = MergeTC bs '[] res-- collapsing this to the other case
--  MergeTC ( '(a,va) ': as) ( '(b,vb) ': bs) res = StableCombine '(a,va) '(b,vb) (CmpSymbol a b) as bs res

type family MergeRec   (x :: [(Symbol,k)]) (y :: [(Symbol,k)])  :: [(Symbol,k) ]  where
   MergeRec as '[]  =  as
   MergeRec '[] bs  =  bs
   MergeRec ( '(a,va) ': as) ( '(b,vb) ': bs)  = StableCombineRec '(a,va) '(b,vb) (CmpSymbol a b) as bs


type family StableCombineRec (a :: k) (b :: k) (s :: Ordering)
      (as :: [k]) (bs :: [k])    :: [k ] where
  StableCombineRec a b 'EQ as bs res =  TypeError ('Text "can't use duplicate keys")
    --- MergeTC as bs (a ': b ': res)
  StableCombineRec a b 'GT as bs res = a ':  MergeRec as (b ': bs)
  StableCombineRec a b 'LT as bs res = b ': MergeRec (a ': as) bs

type family Merge (x :: [(Symbol,k)]) (y :: [(Symbol,k)])   :: [(Symbol,k) ] where
  Merge x y = MergeRec x y {-'[]-}

--type family StableCombine (a :: k) (b :: k) (s :: Ordering)
--      (as :: [k]) (bs :: [k]) (res :: [k])   :: [k ] where
--  StableCombine a b 'EQ as bs res =  TypeError ('Text "can't use duplicate keys")
--    --- MergeTC as bs (a ': b ': res)
--  StableCombine a b 'GT as bs res =  MergeTC as (b ': bs) (a ': res)
--  StableCombine a b 'LT as bs res = MergeTC (a ': as) bs (b ': res)


--type family SplitTC (a :: [k]) (odds :: [k]) (evens :: [k] ) :: ([k],[k])  where
--  SplitTC '[]  odds evens = '(Reverse odds, Reverse evens)
--  SplitTC (a ': b ': rest ) odds evens = SplitTC rest (a ': odds) (b ': evens)
--  SplitTC (a ': '[]) odds evens = '( Reverse (a ': odds), Reverse evens )


--type family Atomize (ls :: [k]) :: [[k]]   where
--  Atomize ls  = AtomizeTC ls '[]

--type family AtomizeTC (ls :: [k] ) (res :: [[k]])  :: [[k]] where
--  AtomizeTC '[] res = Reverse res
--  AtomizeTC (a ': rest) res = AtomizeTC rest (( a ': '[]) ': res)


type family Sort (input :: [(Symbol,k)]) :: [(Symbol,k)] where
    Sort '[] = '[]
    Sort ( a ': '[]) = ( a ': '[])
    Sort ls = IterMerge (Atomize ls)

type family IterMerge (lss :: [[(Symbol,k)]] ) :: [(Symbol,k)] where
  IterMerge (ls ': '[]) = Reverse ls -- i dont know why, but I need this revrse here
  IterMerge ls = IterMergeTC ls '[]


type family IterMergeTC (lss :: [[(Symbol,k)]] ) (res :: [[(Symbol,k)]]) :: [(Symbol,k)] where
  IterMergeTC (a ': b ': rest) res = IterMergeTC rest (Merge  a b ':  res)
  IterMergeTC (a ': '[]) res = IterMerge( Reverse (a ': res))
  IterMergeTC '[] res = IterMerge (Reverse res )


type family IsSorted (x :: [(Symbol,k)]) :: [(Symbol,k)] where
  IsSorted x = IsSortedTC x x

type family IsSortedTC (x :: [(Symbol,k)]) (y :: [(Symbol,k)]) :: [(Symbol,k)] where
  IsSortedTC '[] res  = res
  IsSortedTC (a ': '[]) res  =  res
  IsSortedTC ('(a,_va) ': '(b,_vb) ': rest) res = SwitchingChecker a b (CmpSymbol a b) rest res

type family SwitchingChecker (sa :: Symbol) (sb :: Symbol) (o :: Ordering)
      (remainder :: [(Symbol,k)]) (res :: [(Symbol,k)])   :: [(Symbol,k)] where
  SwitchingChecker sa sb 'EQ  remainder res =
      TypeError ('Text "conflicting fields are bad!" ':$$: 'ShowType '(sa,sb))
  SwitchingChecker sa sb 'LT  remainder res = IsSortedTC remainder res
  SwitchingChecker sa sb 'GT remainder  res =
      TypeError ('Text "unsorted fields are bad! offendingKeys are" ':$$:  'ShowType '(sa,sb))



newtype Sorted a = DefSorted a
    deriving (Eq, Show)


_testExample :: forall (x ::  [(Symbol, *)] ) (y :: [(Symbol, *)])  .
    ( --  y ~ IsSorted y ,
    --  (Sort x) ~ Sort y ,
    -- (y1 :: [(Symbol, *)] ) ~ [ '("z",Double),'("x",Int), '("x", ())],
     (y :: [(Symbol, *)] )~ (Sort ['("z",Double),'("x",Int), '("x", ())] ),
     (x :: [(Symbol, *)] )~  (Sort [ '("c",() ) , '("x", Int), '("z",Double)])
    )
  => (Proxy  ( y :: [(Symbol, *)] ))
_testExample = Proxy ::( Proxy ( (Sort [ '("c",() ) , '("x", Int), '("z",Double)])))
