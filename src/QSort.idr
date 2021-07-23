module QSort

import Data.So
import Data.List
import Decidable.Order
import Data.List.Elem
import Data.List.Quantifiers
import Data.Nat
import Data.Nat.Order
import Data.Nat.Views
import Data.Vect

%default total

public export
data NonEmptySorted : (lte': a -> a -> Type) -> List a -> Type where
    One : NonEmptySorted lte' [x]
    Many : {x: a} -> (lte' x y) -> NonEmptySorted lte' (y :: xs) -> NonEmptySorted lte' (x :: y :: xs)


public export
data Sorted : (lte': a -> a -> Type) -> List a -> Type where
    Empty : Sorted lte' []
    NonEmpty : NonEmptySorted lte' v -> Sorted lte' v

public export
data Permutation : (xs: List a) -> (xs': List a) -> Type where 
    PermNil : Permutation [] []  
    PermCons : Permutation xs xs' -> Permutation (x :: xs) (x :: xs')
    PermSwap : Permutation (x :: y :: xs) (y :: x :: xs)
    PermTrans : {ys: List a} -> Permutation xs ys -> Permutation ys zs -> Permutation xs zs  

public export
permutationRefl : {xs: List a} -> Permutation xs xs
permutationRefl {xs = []} = PermNil 
permutationRefl {xs = (x :: xs)} = PermCons permutationRefl {xs = xs}

public export
permutationSym : Permutation xs ys -> Permutation ys xs
permutationSym PermNil = PermNil 
permutationSym (PermCons xs) = PermCons (permutationSym xs) 
permutationSym PermSwap = PermSwap 
permutationSym (PermTrans x y) = PermTrans (permutationSym y) (permutationSym x)


public export
data Partition : (lte': a -> a -> Type) -> (p: a) -> (xs: List a) -> Type where
    MkPartition : {ys, zs: List a} -> (0 _ : All (\x => lte' x p) ys) -> (0 _ : All (\x => lte' p x) zs) ->
                  (0 _ : Permutation xs (ys ++ zs)) ->
                  Partition lte' p xs


public export
permutationConcat : {xs, xs', zs: List a} -> Permutation xs xs' -> Permutation (xs ++ zs) (xs' ++ zs)
permutationConcat PermNil = permutationRefl 
permutationConcat (PermCons xs) = PermCons (permutationConcat xs) 
permutationConcat PermSwap = PermSwap 
permutationConcat (PermTrans p1 p2) = 
    let ih1 = permutationConcat p1 in 
    let ih2 = permutationConcat p2 in
    PermTrans ih1 ih2


public export
permutationComm : {xs, ys: List a} -> Permutation (xs ++ ys) (ys ++ xs)
permutationComm {xs = xs} {ys = []} = 
    rewrite appendNilRightNeutral xs in permutationRefl 
permutationComm {xs = []} {ys = (y :: ys)} = 
    rewrite appendNilRightNeutral ys in permutationRefl 
permutationComm {xs = (x :: xs)} {ys = (y :: ys)} = 
    let ih1 = permutationComm {xs = xs} {ys = ys} in 
    let ih2 = permutationComm {xs = (x::xs)} {ys = ys} in 
    let ih3 = permutationComm {xs = xs} {ys = (y::ys)} in 
    let p1 = PermCons $ PermTrans ih3 (PermCons (permutationSym ih1)) in 
    let p2 = PermTrans PermSwap (PermCons ih2) in PermTrans p1 p2

public export
permutationConcatReverse : {xs, xs', zs: List a} -> Permutation xs xs' -> Permutation (zs ++ xs) (zs ++ xs')
permutationConcatReverse px = 
    let p1 = permutationConcat px {zs=zs} in 
    let p2 = permutationComm {xs=xs} {ys=zs} in 
    let p3 = PermTrans (permutationSym p1) p2 in 
    PermTrans (permutationSym p3) (permutationComm)

public export
0 permutationConcatTrans : {xs, xs', ys, ys' : List a} -> 
                         Permutation xs xs' -> Permutation ys ys' -> Permutation (xs ++ ys) (xs' ++ ys')
permutationConcatTrans PermNil py = py 
permutationConcatTrans (PermCons px) py = PermCons (permutationConcatTrans px py) 
permutationConcatTrans PermSwap py = 
    let p1 = permutationConcatReverse py in 
    let p2 = PermSwap in 
    let p3 = PermCons (PermCons p1) in 
    PermTrans p2 p3
permutationConcatTrans (PermTrans x y) py = 
    let ih1 = permutationConcatTrans x py in 
    let ih2 = permutationConcatTrans y py in 
    let p1 = permutationSym (permutationConcatReverse py) in 
    PermTrans (PermTrans ih1 p1) ih2

public export
0 permutationLemma : {x: a} -> {xs, ys, zs: List a} -> Permutation xs (ys ++ zs) -> Permutation (x :: xs) (ys ++ (x :: zs))
permutationLemma perm = 
    PermTrans (PermCons {x=x} $ PermTrans perm (permutationComm {xs=ys} {ys=zs}))
                (permutationComm {xs=(x::zs)} {ys=ys})

public export
partition : (o: Ordered a lte') => (p: a) -> (xs: List a) -> Partition lte' p xs 
partition p [] = MkPartition [] [] PermNil   
partition p (x :: xs) = 
    case order @{o} x p of
        Left lte => 
            let (MkPartition allLte allGte perm) = partition @{o} p xs
            in MkPartition (lte::allLte) allGte (PermCons perm)
        Right gte => 
            let (MkPartition allLte allGte perm) = partition @{o} p xs
            in MkPartition allLte (gte::allGte) (permutationLemma perm) 

public export
0 permutationAll : All p xs -> Permutation xs ws -> All p ws 
permutationAll (x :: y :: xs) PermSwap = y :: x :: xs  
permutationAll all PermNil = [] 
permutationAll (x :: xs) (PermCons c) = x :: permutationAll xs c
permutationAll all (PermTrans a b) = 
    permutationAll (permutationAll all a) b


public export
0 lastAll : {xs: List a} -> {auto pf: NonEmpty xs} -> All p xs -> p (last xs)
lastAll [] impossible
lastAll (p :: ps) = 
    case ps of
        [] => p
        (q :: qs) => lastAll (q :: qs)

public export
appendSorted : {xs : List a} -> {pf: NonEmpty xs} -> 
               Sorted lte' xs -> lte' (last xs) p -> Sorted lte' (xs ++ [p])
appendSorted Empty pfLteLast impossible 
appendSorted (NonEmpty y) pfLteLast = 
    case y of 
        One => NonEmpty (Many pfLteLast One) 
        Many pfLte rest => 
            let (NonEmpty ne) = appendSorted (NonEmpty rest) pfLteLast in 
            NonEmpty (Many pfLte ne) 

public export
0 sortingLemma : {xs: List a} -> {auto prfXs: NonEmpty xs} -> 
               Sorted lte' xs -> Sorted lte' (z::zs) -> lte' (last xs) z -> Sorted lte' (xs ++ (z::zs))
sortingLemma Empty sortYs inOrder impossible 
sortingLemma (NonEmpty neXs) (NonEmpty neYs) inOrder = 
    case neXs of
        One => NonEmpty (Many inOrder neYs) 
        Many pfLte rst => 
            let (NonEmpty rst') = sortingLemma (NonEmpty rst) (NonEmpty neYs) inOrder in
            NonEmpty (Many pfLte rst')


public export
data SortedList : (lte': a -> a -> Type) -> (xs: List a) -> Type where
    MkSortedList : (ws: List a) -> (0 srtd : Sorted lte' ws) -> (0 perm : Permutation xs ws) -> SortedList lte' xs 

public export
quicksort : (o: Ordered a lte') => (xs: List a) -> SortedList lte' xs
quicksort [] = MkSortedList [] Empty PermNil
quicksort (p :: xs) = 
    let (MkPartition {ys=ys} {zs=zs} ltp gtp perm) = partition @{o} p xs in 
    let (MkSortedList lhs stdLhs permLhs) = quicksort @{o} ys in 
    let (MkSortedList rhs stdRhs permRhs) = quicksort @{o} zs in 
    let 0 lteLhs : All (\x => lte' x p) lhs = permutationAll ltp permLhs in
    let 0 gteRhs : All (\x => lte' p x) rhs = permutationAll gtp permRhs in
    let 0 consPRhs : Sorted lte' (p :: rhs) = 
        case stdRhs of   
            Empty => NonEmpty (One) 
            NonEmpty One => 
                let [pfGte] = gteRhs in NonEmpty (Many pfGte One) 
            NonEmpty (Many pf1 rst) =>
                let (pfGte :: _) = gteRhs in NonEmpty (Many pfGte (Many pf1 rst))
    in
    let 0 permFinal = permutationLemma {x=p} (PermTrans perm (permutationConcatTrans permLhs permRhs)) in 
    let 0 srtd = 
        case lteLhs of 
            [] => consPRhs
            (lte::ltes) => 
                let lastLhs = lastAll lteLhs in
                sortingLemma {lte'=lte'} stdLhs consPRhs lastLhs
    in
    (MkSortedList (lhs ++ (p :: rhs)) srtd permFinal)
