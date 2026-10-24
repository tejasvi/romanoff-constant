import K45.G.L9_004
import K45.Orb.O042
import K45.Orb.O043
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_042 : c9_042.filterMap orbF = K45.Orb.orbs042 := by
  decide +kernel

theorem oc_043 : c9_043.filterMap orbF = K45.Orb.orbs043 := by
  decide +kernel

end K45.S
