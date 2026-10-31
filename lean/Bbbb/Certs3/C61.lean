import Bbbb.Certs3.Data

namespace Bbbb

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def chunk3_61 : Tree :=
  .node 3 [.leaf (.per 0 4 [false, false, false] [false] .any .blank), .leaf (.per 1 3 [false, false] [false] .any .blank), .leaf (.per 1 4 [false, false] [false] .any .blank), .leaf (.per 0 4 [] [false, false] .blank .any), .leaf (.per 1 3 [] [false, false] .blank .any), .leaf (.per 1 4 [false, false] [false] .any .blank), .leaf (.per 3 2 [] [true] .blank .blank), .node 5 [.node 6 [.leaf (.per 0 7 [false, false, false] [false] .any .blank), .leaf (.per 1 6 [false, false] [false] .any .blank), .leaf (.per 1 7 [false, false] [false] .any .blank), .leaf (.per 0 7 [] [false, false] .blank .any), .leaf (.per 1 6 [false, false] [false] .any .blank), .leaf (.per 1 7 [false, false] [false] .any .blank), .leaf (.per 3 5 [] [true] .blank .blank), .leaf (.per 4 3 [true, false] [false] .any .blank), .leaf (.per 4 7 [true, false] [false] .any .blank), .leaf (.per 7 7 [] [false, true] .blank .any), .hold 729, .leaf (.per 3 5 [] [true] .blank .blank)], .leaf (.per 3 3 [] [true] .blank .blank), .leaf (.per 1 7 [false, false] [false] .any .blank), .leaf (.per 0 6 [] [false, false] .blank .any), .leaf (.per 6 5 [] [false, false, true] .blank .any), .hold 730, .node 6 [.leaf (.per 4 4 [true, false] [false] .any .blank), .leaf (.per 4 6 [true, false] [false] .any .blank), .leaf (.per 1 7 [false, false] [false] .any .blank), .leaf (.per 0 8 [] [false, false] .blank .any), .leaf (.per 3 4 [] [true] .blank .blank), .leaf (.per 3 6 [] [true] .blank .blank), .leaf (.per 7 5 [true, true] [false] .any .blank), .leaf (.per 7 3 [true, true] [false] .any .blank), .leaf (.per 4 7 [true, false] [false] .any .blank), .leaf (.per 8 8 [] [false, true] .blank .any), .leaf (.per 9 5 [true, true] [false] .any .blank), .leaf (.per 5 2 [] [true, true] .blank .blank)], .leaf (.per 7 3 [true, true] [false] .any .blank), .leaf (.per 4 7 [true, false] [false] .any .blank), .leaf (.per 6 6 [] [false, true] .blank .any), .leaf (.per 11 5 [true, true, true] [false] .any .blank), .hold 731], .leaf (.per 4 4 [true] [false] .any .blank), .leaf (.per 1 4 [] [false, false] .blank .any), .leaf (.per 4 3 [] [false, true] .blank .any), .leaf (.per 2 2 [] [false, true, false] .blank .any)]

theorem chunk3_61_ok : checkTree 2 127 holds3 [some 5, none, some 12, none, some 2, none] chunk3_61 = true := by decide +kernel

end Bbbb
