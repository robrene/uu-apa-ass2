import Fun
import ControlFlowAnalysis

mkIdFn ann var = Fn ann var (Var var)

e_5_13 = Op (Op part1 Plus part2) Plus part3
  where part1 = App (Var "f") (Fn "X" "x" (Op (Var "x") Plus (Const $ CInt 1)))
        part2 = App (Var "f") (Fn "Y" "y" (Op (Var "y") Plus (Const $ CInt 2)))
        part3 = App (Fn "Z" "z" (Op (Var "z") Plus (Const $ CInt 3))) (Const $ CInt 4)

e_5_14 = App part1 part2
  where part1 = mkIdFn "X" "x"
        part2 = mkIdFn "Y" "y"

e_5_19 = Let "g" part1 (App (Var "g") (mkIdFn "Z" "z"))
  where part1 = Fun "F" "f" "x" (App (Var "f") (mkIdFn "Y" "y"))
