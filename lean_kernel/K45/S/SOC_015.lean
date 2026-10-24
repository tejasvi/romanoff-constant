import K45.G.L9_003
import K45.Orb.O030
import K45.Orb.O031
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_030 : c9_030.filterMap orbF = K45.Orb.orbs030 := by
  decide +kernel

theorem oc_031 : c9_031.filterMap orbF = K45.Orb.orbs031 := by
  decide +kernel

end K45.S
