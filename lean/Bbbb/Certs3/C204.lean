import Bbbb.Certs3.Data

namespace Bbbb

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def chunk3_204 : Tree :=
  .node 3 [.leaf (.per 0 4 [false, false] [false] .any .blank), .leaf (.per 4 1 [false] [false] .any .blank), .leaf (.per 3 1 [false] [false] .any .blank), .leaf (.per 0 4 [] [false, false] .blank .any), .leaf (.per 4 1 [false] [false] .any .blank), .leaf (.per 3 1 [] [false, false] .blank .any), .leaf (.per 6 3 [] [false, false, true] .blank .any), .leaf (.per 5 1 [false] [false] .any .blank), .leaf (.per 4 1 [true] [false] .any .blank), .leaf (.per 3 4 [] [false, false] .blank .any), .leaf (.per 1 3 [] [false, true, false] .blank .any), .leaf (.per 4 1 [] [false, true] .blank .any)]

theorem chunk3_204_ok : checkTree 2 127 holds3 [some 11, none, some 2, some 6, none, none] chunk3_204 = true := by decide +kernel

end Bbbb
