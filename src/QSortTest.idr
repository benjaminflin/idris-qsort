module QSortTest

import QSort 
import Data.Nat
import Data.List
import Data.Nat.Order
import Data.Int.Order
import Control.Order

StronglyConnex Nat LTE where
    order x y = 
        case lte x y of 
            Yes pf => Left pf
            No pf => Right . lteSuccLeft $ notLTEImpliesGT pf 

StronglyConnex Int LTE where
    order x y = 
        case decide_LTE_GT x y of 
            Left pf => Left pf 
            Right pf => Right $ inject_LT_LTE pf

main : IO ()
main = do
    let (MkSortedList sorted _ _) = quicksort {a=Int} {lte'=LTE} [100..0]
    print sorted
    putStrLn "\n"
