import K45.G.B9_005
import K45.G.M9_005
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem m9_005 : mergeRuns B9g_005 = m9_005 := by
  decide +kernel

end K45.S
