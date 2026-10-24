import K45.G.B8
import K45.G.L8
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem m8 : mergeRuns B8s = L8 := by
  decide +kernel

theorem p8 : strictPos L8 = true := by
  decide +kernel

end K45.S
