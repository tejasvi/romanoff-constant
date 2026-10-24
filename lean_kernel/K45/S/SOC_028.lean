import K45.G.L9_005
import K45.Orb.O056
import K45.Orb.O057
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_056 : c9_056.filterMap orbF = K45.Orb.orbs056 := by
  decide +kernel

theorem oc_057 : c9_057.filterMap orbF = K45.Orb.orbs057 := by
  decide +kernel

end K45.S
