module QSortTest

import QSort 
import Data.Nat
import Data.Nat.Order
import Decidable.Order

main : IO ()
main = let (MkSortedList sorted) = quicksort' {a=Nat} {lte'=LTE} [10..0] in print sorted
