import K45.G.L9_005
import K45.Orb.O058
import K45.Orb.O059
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_058 : c9_058.filterMap orbF = K45.Orb.orbs058 := by
  decide +kernel

theorem oc_059 : c9_059.filterMap orbF = K45.Orb.orbs059 := by
  decide +kernel

end K45.S
