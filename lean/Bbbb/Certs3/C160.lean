import Bbbb.Certs3.Data

namespace Bbbb

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def chunk3_160 : Tree :=
  .node 3 [.leaf (.per 0 4 [false] [false] .any .blank), .leaf (.per 3 1 [false] [false] .any .blank), .leaf (.per 4 1 [] [false, false] .blank .any), .leaf (.per 0 4 [false] [false] .any .blank), .leaf (.per 3 1 [] [false, false] .blank .any), .leaf (.per 4 1 [] [false, false] .blank .any), .leaf (.per 3 4 [false] [false] .any .blank), .leaf (.per 4 1 [true] [false] .any .blank), .leaf (.per 1 3 [true, false] [false] .any .blank), .leaf (.per 6 3 [false, true] [false] .any .blank), .leaf (.per 4 1 [] [false, true] .blank .any), .leaf (.per 5 1 [] [false, false] .blank .any)]

theorem chunk3_160_ok : checkTree 2 127 holds3 [some 9, none, none, none, some 6, some 2] chunk3_160 = true := by decide +kernel

end Bbbb
