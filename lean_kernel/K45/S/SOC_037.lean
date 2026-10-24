import K45.G.L9_007
import K45.Orb.O074
import K45.Orb.O075
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_074 : c9_074.filterMap orbF = K45.Orb.orbs074 := by
  decide +kernel

theorem oc_075 : c9_075.filterMap orbF = K45.Orb.orbs075 := by
  decide +kernel

end K45.S
