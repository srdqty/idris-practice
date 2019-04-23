my_map : %static (a -> b) -> List a -> List b
my_map f [] = []
my_map f (x :: xs) = f x :: my_map f xs

doubleAll : List Int -> List Int
doubleAll xs = my_map (*2) xs
