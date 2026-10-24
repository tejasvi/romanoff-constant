import K45.G.B9_001
import K45.G.M9_001
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem m9_001 : mergeRuns B9g_001 = m9_001 := by
  decide +kernel

end K45.S
