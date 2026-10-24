import K45.G.L9_013
import K45.Orb.O138
import K45.Orb.O139
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_138 : c9_138.filterMap orbF = K45.Orb.orbs138 := by
  decide +kernel

theorem oc_139 : c9_139.filterMap orbF = K45.Orb.orbs139 := by
  decide +kernel

end K45.S
