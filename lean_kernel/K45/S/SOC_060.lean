import K45.G.L9_012
import K45.Orb.O120
import K45.Orb.O121
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_120 : c9_120.filterMap orbF = K45.Orb.orbs120 := by
  decide +kernel

theorem oc_121 : c9_121.filterMap orbF = K45.Orb.orbs121 := by
  decide +kernel

end K45.S
