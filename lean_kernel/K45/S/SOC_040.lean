import K45.G.L9_008
import K45.Orb.O080
import K45.Orb.O081
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_080 : c9_080.filterMap orbF = K45.Orb.orbs080 := by
  decide +kernel

theorem oc_081 : c9_081.filterMap orbF = K45.Orb.orbs081 := by
  decide +kernel

end K45.S
