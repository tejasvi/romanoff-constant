import K45.G.L9_009
import K45.Orb.O098
import K45.Orb.O099
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_098 : c9_098.filterMap orbF = K45.Orb.orbs098 := by
  decide +kernel

theorem oc_099 : c9_099.filterMap orbF = K45.Orb.orbs099 := by
  decide +kernel

end K45.S
