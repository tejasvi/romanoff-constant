import K45.G.L9_010
import K45.Orb.O106
import K45.Orb.O107
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_106 : c9_106.filterMap orbF = K45.Orb.orbs106 := by
  decide +kernel

theorem oc_107 : c9_107.filterMap orbF = K45.Orb.orbs107 := by
  decide +kernel

end K45.S
