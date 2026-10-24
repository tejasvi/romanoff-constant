import K45.G.B9_010
import K45.G.M9_010
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem m9_010 : mergeRuns B9g_010 = m9_010 := by
  decide +kernel

end K45.S
