import K45.G.L9_012
import K45.Orb.O122
import K45.Orb.O123
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_122 : c9_122.filterMap orbF = K45.Orb.orbs122 := by
  decide +kernel

theorem oc_123 : c9_123.filterMap orbF = K45.Orb.orbs123 := by
  decide +kernel

end K45.S
