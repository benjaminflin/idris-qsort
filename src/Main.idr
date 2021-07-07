module Main

import Data.So
import Data.List
import Decidable.Order
import Data.List.Elem
import Data.List.Quantifiers
import Data.Nat
import Data.Nat.Views

%default total

data NonEmptySorted : (lte': a -> a -> Type) -> List a -> Type where
    One : NonEmptySorted lte' [x]
    Many : {x: a} -> (lte' x y) -> NonEmptySorted lte' (y :: xs) -> NonEmptySorted lte' (x :: y :: xs)

data Sorted : (lte': a -> a -> Type) -> List a -> Type where
    Empty : Sorted lte' []
    NonEmpty : NonEmptySorted lte' v -> Sorted lte' v

data Permutation : (xs: List a) -> (xs': List a) -> Type where 
    PermNil : Permutation [] []  
    PermCons : Permutation xs xs' -> Permutation (x :: xs) (x :: xs')
    PermSwap : Permutation (x :: y :: xs) (y :: x :: xs)
    PermTrans : {ys: List a} -> Permutation xs ys -> Permutation ys zs -> Permutation xs zs  

permutationRefl : {xs: List a} -> Permutation xs xs
permutationRefl {xs = []} = PermNil 
permutationRefl {xs = (x :: xs)} = PermCons permutationRefl {xs = xs}

permutationSym : Permutation xs ys -> Permutation ys xs
permutationSym PermNil = PermNil 
permutationSym (PermCons xs) = PermCons (permutationSym xs) 
permutationSym PermSwap = PermSwap 
permutationSym (PermTrans x y) = PermTrans (permutationSym y) (permutationSym x)


data Partition : (lte': a -> a -> Type) -> (p: a) -> (xs: List a) -> Type where
    MkPartition : {ys, zs: List a} -> All (\x => lte' x p) ys -> All (\x => lte' p x) zs ->
                  Permutation xs (ys ++ zs) ->
                  Partition lte' p xs


permutationConcat : {xs, xs', zs: List a} -> Permutation xs xs' -> Permutation (xs ++ zs) (xs' ++ zs)
permutationConcat PermNil = permutationRefl 
permutationConcat (PermCons xs) = PermCons (permutationConcat xs) 
permutationConcat PermSwap = PermSwap 
permutationConcat (PermTrans p1 p2) = 
    let ih1 = permutationConcat p1 in 
    let ih2 = permutationConcat p2 in
    PermTrans ih1 ih2


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

permutationConcatReverse : {xs, xs', zs: List a} -> Permutation xs xs' -> Permutation (zs ++ xs) (zs ++ xs')
permutationConcatReverse px = 
    let p1 = permutationConcat px {zs=zs} in 
    let p2 = permutationComm {xs=xs} {ys=zs} in 
    let p3 = PermTrans (permutationSym p1) p2 in 
    PermTrans (permutationSym p3) (permutationComm)

permutationAppendNil : {xs, xs', ys: List a} -> Permutation xs xs' -> Permutation xs (xs' ++ ys) -> ys = []
permutationAppendNil px = believe_me 

permutationConcatLemma : {xs, xs', ys, ys': List a} -> Permutation xs xs' -> Permutation (xs ++ ys) (xs ++ ys') -> Permutation (xs ++ ys) (xs' ++ ys')
permutationConcatLemma px pxy = 
    case ys of 
        [] => rewrite appendNilRightNeutral xs in ?pcl_5
        (z::zs) => ?pcl_6

permutationConcatTrans : {xs, xs', ys, ys' : List a} -> 
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

permutationLemma : {x: a} -> {xs, ys, zs: List a} -> Permutation xs (ys ++ zs) -> Permutation (x :: xs) (ys ++ (x :: zs))
permutationLemma perm = 
    PermTrans (PermCons {x=x} $ PermTrans perm (permutationComm {xs=ys} {ys=zs}))
                (permutationComm {xs=(x::zs)} {ys=ys})

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

permutationAll : All p xs -> Permutation xs ws -> All p ws 
permutationAll all PermNil = [] 
permutationAll (x :: xs) (PermCons c) = x :: permutationAll xs c
permutationAll (x :: y :: xs) PermSwap = y :: x :: xs  
permutationAll all (PermTrans a b) = 
    permutationAll (permutationAll all a) b


lastAll : {xs: List a} -> {auto pf: NonEmpty xs} -> All p xs -> p (last xs)
lastAll [] impossible
lastAll (p :: ps) = 
    case ps of
        [] => p
        (q :: qs) => lastAll (q :: qs)

appendSorted : {xs : List a} -> {pf: NonEmpty xs} -> 
               Sorted lte' xs -> lte' (last xs) p -> Sorted lte' (xs ++ [p])
appendSorted Empty pfLteLast impossible 
appendSorted (NonEmpty y) pfLteLast = 
    case y of 
        One => NonEmpty (Many pfLteLast One) 
        Many pfLte rest => 
            let (NonEmpty ne) = appendSorted (NonEmpty rest) pfLteLast in 
            NonEmpty (Many pfLte ne) 

sortingLemma : {xs: List a} -> {prfXs: NonEmpty xs} -> 
               Sorted lte' xs -> Sorted lte' (z::zs) -> lte' (last xs) z -> Sorted lte' (xs ++ (z::zs))
sortingLemma Empty sortYs inOrder impossible 
sortingLemma (NonEmpty neXs) (NonEmpty neYs) inOrder = 
    case neXs of
        One => NonEmpty (Many inOrder neYs) 
        Many pfLte rst => 
            let (NonEmpty rst') = sortingLemma (NonEmpty rst) (NonEmpty neYs) inOrder in
            NonEmpty (Many pfLte rst')


quicksort : (o: Ordered a lte') => (xs: List a) -> (ws: List a ** (Sorted lte' ws, Permutation xs ws))
quicksort [] = ([] ** (Empty, PermNil))
quicksort (p :: xs) = 
    let (MkPartition {ys=ys} {zs=zs} ltp gtp perm) = partition @{o} p xs in 
    let (lhs ** (stdLhs, permLhs)) = quicksort @{o} ys in 
    let (rhs ** (stdRhs, permRhs)) = quicksort @{o} zs in 
    let lteLhs : All (\x => lte' x p) lhs = permutationAll ltp permLhs in
    let gteRhs : All (\x => lte' p x) rhs = permutationAll gtp permRhs in
    let consPRhs : Sorted lte' (p :: rhs) = 
        case stdRhs of   
            Empty => NonEmpty (One) 
            NonEmpty One => 
                let [pfGte] = gteRhs in NonEmpty (Many pfGte One) 
            NonEmpty (Many pf1 rst) =>
                let (pfGte :: _) = gteRhs in NonEmpty (Many pfGte (Many pf1 rst))
    in
    let permFinal = permutationLemma {x=p} (PermTrans perm (permutationConcatTrans permLhs permRhs)) in 
    case lteLhs of 
        [] => ((p :: rhs) ** (consPRhs, permFinal))
        (lte::ltes) => 
            let lastLhs = lastAll lteLhs in
            let sortL = sortingLemma stdLhs consPRhs lastLhs in
            (lhs ++ (p :: rhs) ** (sortL, permFinal))


main : IO ()
main = print "hello" 