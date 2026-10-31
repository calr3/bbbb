import Bbbb.Certs3.Data

namespace Bbbb

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def chunk3_28 : Tree :=
  .node 3 [.leaf (.per 0 4 [false] [false] .any .blank), .leaf (.per 1 4 [false] [false] .any .blank), .leaf (.per 1 3 [false] [false] .any .blank), .leaf (.per 0 4 [false] [false] .any .blank), .leaf (.per 1 4 [] [false, false, false] .blank .any), .leaf (.per 1 3 [] [false, false, false] .blank .any), .leaf (.per 1 4 [false] [false] .any .blank), .leaf (.per 2 2 [true, false] [false] .any .blank), .leaf (.per 4 3 [true] [false] .any .blank), .leaf (.per 3 2 [] [true] .blank .blank), .leaf (.per 4 4 [] [false, true] .blank .any), .node 5 [.leaf (.per 0 6 [false] [false] .any .blank), .hold 308, .leaf (.per 6 5 [false, true] [false] .any .blank), .node 6 [.leaf (.per 0 7 [false] [false] .any .blank), .leaf (.per 1 7 [] [false, false, false] .blank .any), .leaf (.per 1 6 [false, false] [false] .any .blank), .leaf (.per 0 7 [] [false, false, false, false] .blank .any), .leaf (.per 1 7 [] [false, false, false] .blank .any), .leaf (.per 1 6 [] [false, false, false] .blank .any), .leaf (.per 7 7 [true] [false] .any .blank), .leaf (.per 3 5 [] [true] .blank .blank), .hold 309, .leaf (.per 3 5 [] [true] .blank .blank), .leaf (.per 4 7 [] [false, true, false] .blank .any), .leaf (.per 4 3 [] [false, true, false] .blank .any)], .leaf (.per 1 7 [] [false, false, false] .blank .any), .leaf (.per 3 3 [] [true] .blank .blank), .leaf (.per 6 6 [true] [false] .any .blank), .hold 310, .leaf (.per 11 5 [] [false, true, true, true] .blank .any), .node 6 [.leaf (.per 0 8 [false] [false] .any .blank), .leaf (.per 3 6 [] [true] .blank .blank), .leaf (.per 3 4 [] [true] .blank .blank), .leaf (.per 4 4 [] [false, true, false] .blank .any), .leaf (.per 1 7 [] [false, false, false] .blank .any), .leaf (.per 4 6 [] [false, true, false] .blank .any), .leaf (.per 8 8 [true] [false] .any .blank), .leaf (.per 5 2 [true] [true] .blank .blank), .leaf (.per 9 5 [] [false, true, true] .blank .any), .leaf (.per 7 5 [] [false, true, true] .blank .any), .leaf (.per 4 7 [] [false, true, false] .blank .any), .leaf (.per 7 3 [] [false, true, true] .blank .any)], .leaf (.per 4 7 [] [false, true, false] .blank .any), .leaf (.per 7 3 [] [false, true, true] .blank .any)]]

theorem chunk3_28_ok : checkTree 2 127 holds3 [some 3, none, some 6, none, some 8, none] chunk3_28 = true := by decide +kernel

end Bbbb
