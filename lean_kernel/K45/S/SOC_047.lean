import K45.G.L9_009
import K45.Orb.O094
import K45.Orb.O095
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_094 : c9_094.filterMap orbF = K45.Orb.orbs094 := by
  decide +kernel

theorem oc_095 : c9_095.filterMap orbF = K45.Orb.orbs095 := by
  decide +kernel

end K45.S
