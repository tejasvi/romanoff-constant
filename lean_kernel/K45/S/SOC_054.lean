import K45.G.L9_010
import K45.Orb.O108
import K45.Orb.O109
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_108 : c9_108.filterMap orbF = K45.Orb.orbs108 := by
  decide +kernel

theorem oc_109 : c9_109.filterMap orbF = K45.Orb.orbs109 := by
  decide +kernel

end K45.S
