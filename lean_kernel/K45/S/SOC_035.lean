import K45.G.L9_007
import K45.Orb.O070
import K45.Orb.O071
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_070 : c9_070.filterMap orbF = K45.Orb.orbs070 := by
  decide +kernel

theorem oc_071 : c9_071.filterMap orbF = K45.Orb.orbs071 := by
  decide +kernel

end K45.S
