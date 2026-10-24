import K45.G.L9_010
import K45.Orb.O100
import K45.Orb.O101
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_100 : c9_100.filterMap orbF = K45.Orb.orbs100 := by
  decide +kernel

theorem oc_101 : c9_101.filterMap orbF = K45.Orb.orbs101 := by
  decide +kernel

end K45.S
