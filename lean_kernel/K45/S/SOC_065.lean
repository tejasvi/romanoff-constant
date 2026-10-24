import K45.G.L9_013
import K45.Orb.O130
import K45.Orb.O131
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_130 : c9_130.filterMap orbF = K45.Orb.orbs130 := by
  decide +kernel

theorem oc_131 : c9_131.filterMap orbF = K45.Orb.orbs131 := by
  decide +kernel

end K45.S
