import K45.G.L9_012
import K45.Orb.O124
import K45.Orb.O125
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_124 : c9_124.filterMap orbF = K45.Orb.orbs124 := by
  decide +kernel

theorem oc_125 : c9_125.filterMap orbF = K45.Orb.orbs125 := by
  decide +kernel

end K45.S
