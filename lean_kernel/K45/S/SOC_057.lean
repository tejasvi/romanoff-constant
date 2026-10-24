import K45.G.L9_011
import K45.Orb.O114
import K45.Orb.O115
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_114 : c9_114.filterMap orbF = K45.Orb.orbs114 := by
  decide +kernel

theorem oc_115 : c9_115.filterMap orbF = K45.Orb.orbs115 := by
  decide +kernel

end K45.S
