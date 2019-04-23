import Data.Vect

calc : Int -> Int
calc x = (x * x) + x

vadd : Num a => Vect n a -> Vect n a -> Vect n a
vadd [] [] = []
vadd (x :: xs) (y :: ys) = x + y :: vadd xs ys

test : List Int -> List Int
test xs = let xs' = fromList xs in toList $ vadd xs' xs'
