-- To get this working in GHC, uncomment the following 2 lines:
--   import Prelude hiding (foldr, uncurry, sum, map, enumFromTo)
--   putInt = print

-- Gratuitous mutual recursion.
factorial n = case n == 0 of True  -> 1
                             False -> n * factorial2 (n - 1)
factorial2 n = case n == 0 of True  -> 1
                              False -> n * factorial (n - 1)
foldr f n xs = case xs of [] -> n
                          (a:as) -> f a (foldr f n as)
uncurry f p = case p of (a, b) -> f a b
sum = foldr (+) 0
enumFromTo a b = case a > b of True  -> []
                               False -> a : enumFromTo (a + 1) b
map f = foldr (\x xs -> f x:xs) []
tenTimes x = 10 * x
f rec n = case n == 0 of True -> 0
                         False -> rec (n - 1) + 2*n - 1
main = do
  putStr "recursion with fix: "
  let fix f = f $ fix f
  putInt $ fix f 100
  putStr "\n5! + (10 + 20 + 30 + 40 + 50) = "
  putInt $ uncurry (+) (factorial 5, sum $ map tenTimes [1..5])
  putStr "\n"
