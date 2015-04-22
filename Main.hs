import Fun
import ControlFlowAnalysis

runWith :: Exp -> TEnv -> IO ()
runWith e env = do putStrLn $ "Expression:            " ++ (ppExp e)
                   putStrLn $ "Annotated type:        " ++ (ppSType t)
                   putStrLn $ "Simple substitutions:\n" ++ (ppSimpleSubst th)
                   putStrLn $ "Constraints:           " ++ (ppConstraints _C)
                    where (t, th, _C) = _W (env, e)

run :: Exp -> IO ()
run e = e `runWith` []

mkIdFn :: String -> String -> Exp
mkIdFn ann var = Fn ann var (Var var)

id_id :: Exp
id_id = App (mkIdFn "X" "x") (mkIdFn "Y" "y")

loop :: Exp
loop = Let "g" g (App (Var "g") (mkIdFn "Z" "z"))
  where g = Fun "F" "f" "x" (App (Var "f") (mkIdFn "Y" "y"))

mkT :: Exp
mkT = Const $ CBool True

mkI :: Int -> Exp
mkI i = Const $ CInt i

e_5_13 :: Exp
e_5_13 = Op (Op part1 Plus part2) Plus part3
  where part1 = App (Var "f") (Fn "X" "x" (Op (Var "x") Plus (mkI 1)))
        part2 = App (Var "f") (Fn "Y" "y" (Op (Var "y") Plus (mkI 2)))
        part3 = App (Fn "Z" "z" (Op (Var "z") Plus (mkI 3))) (mkI 4)

run_example_5_13 = e_5_13 `runWith` [("f", (STyInt -|"φ1"|> STyInt) -|"φ2"|> STyInt)]

pair :: Exp
pair = Pair "p" mkT (mkI 2)

list :: Exp
list = ListCons "3" (mkI 3) $ ListCons "2" (mkI 2) $ ListNil "n"
