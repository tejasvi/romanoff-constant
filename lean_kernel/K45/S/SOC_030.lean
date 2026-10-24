import K45.G.L9_006
import K45.Orb.O060
import K45.Orb.O061
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_060 : c9_060.filterMap orbF = K45.Orb.orbs060 := by
  decide +kernel

theorem oc_061 : c9_061.filterMap orbF = K45.Orb.orbs061 := by
  decide +kernel

end K45.S
