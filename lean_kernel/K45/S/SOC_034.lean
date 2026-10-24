import K45.G.L9_006
import K45.Orb.O068
import K45.Orb.O069
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_068 : c9_068.filterMap orbF = K45.Orb.orbs068 := by
  decide +kernel

theorem oc_069 : c9_069.filterMap orbF = K45.Orb.orbs069 := by
  decide +kernel

end K45.S
