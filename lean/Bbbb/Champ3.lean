import Bbbb.Tree

/-! # The 3-state champion: `1RB1LB_0RC0LA_1LC0LA`, beep A0, boop B1, `g = 127` -/

namespace Bbbb

def champ3 : Machine 3 := PM.toM 2 [some 8, some 11, some 3, some 4, some 12, some 4]

def champ3Cert : Cert := .per 104 24 [] [false, true, false, true, false, true] .blank .any

set_option maxRecDepth 100000 in
theorem champ3_qq : champ3.QQHaltsAt (single 0 false) (single 1 true) 127 :=
  qq_of_cert (c := champ3Cert) (by decide) _ _ 126 (by decide)

end Bbbb
