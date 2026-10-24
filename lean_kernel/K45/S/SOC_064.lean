import K45.G.L9_012
import K45.Orb.O128
import K45.Orb.O129
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_128 : c9_128.filterMap orbF = K45.Orb.orbs128 := by
  decide +kernel

theorem oc_129 : c9_129.filterMap orbF = K45.Orb.orbs129 := by
  decide +kernel

end K45.S
