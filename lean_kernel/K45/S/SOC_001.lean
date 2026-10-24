import K45.G.L9_000
import K45.Orb.O002
import K45.Orb.O003
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_002 : c9_002.filterMap orbF = K45.Orb.orbs002 := by
  decide +kernel

theorem oc_003 : c9_003.filterMap orbF = K45.Orb.orbs003 := by
  decide +kernel

end K45.S
