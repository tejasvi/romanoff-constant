import K45.G.L9_013
import K45.Orb.O136
import K45.Orb.O137
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_136 : c9_136.filterMap orbF = K45.Orb.orbs136 := by
  decide +kernel

theorem oc_137 : c9_137.filterMap orbF = K45.Orb.orbs137 := by
  decide +kernel

end K45.S
