my_pow : Nat -> %static Nat -> Nat
my_pow k Z = 1
my_pow k (S j) = mult k (my_pow k j)

powFn : Nat -> Nat
powFn x = plus (my_pow x (S (S Z))) (S Z)
