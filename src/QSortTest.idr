module QSortTest

import QSort 
import Data.Nat
import Data.List
import Data.Nat.Order
import Decidable.Order

qsort_fast : List Nat -> List Nat
qsort_fast [] = []
qsort_fast (p :: xs) = let (lhs, rhs) = partition (<=p) xs in (qsort_fast lhs) ++ (p :: (qsort_fast rhs))

main : IO ()
main = let (MkSortedList sorted _ _) = quicksort {a=Nat} {lte'=LTE} [100..0] in print sorted
