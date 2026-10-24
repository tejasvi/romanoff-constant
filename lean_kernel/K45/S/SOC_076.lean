import K45.G.L9_015
import K45.Orb.O152
import K45.Orb.O153
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_152 : c9_152.filterMap orbF = K45.Orb.orbs152 := by
  decide +kernel

theorem oc_153 : c9_153.filterMap orbF = K45.Orb.orbs153 := by
  decide +kernel

end K45.S
