
import Data.Maybe
import TRS hiding (s)
-- import Test.Peano
import System.Environment

z   = term "z" []
s x = term "s" [x]
p x = term "p" [x]
fact x y = term "fact" [x,y]
x +: y = term "+" [x,y]
x *: y = term "*" [x,y]

instance Num (TermStatic BasicShape) where 
  fromInteger x = iterate s z !! fromIntegral x
  x + y = x +: y
  x * y = x *: y

benchTRS= [ s x +: y     :-> s(x +: y)
          , z   +: y     :-> y         
          , z   *: y     :-> z
          , s x *: y     :-> y +: (p (s x) *: y)
          , p (s z)      :-> z
          , p (s (s x))  :-> s (p (s x))
          , fact z x     :-> x
          , fact (s x) y :-> fact (p (s x)) (s x *: y)
          ]

y, x :: forall s. TermStatic s
x = Var 0
y = Var 1


test1 = fromJust $ rewrite benchTRS (fact (fromInteger 5) (s x))
test2 = fromJust $ rewrite benchTRS ( 3 * 100 :: TermStatic BasicShape)

main = do
  [arg] <- getArgs
  case read arg of
    1 -> print test1
    2 -> print test2
  `catch`  (\e-> putStrLn "USAGE: main (1|2)") 