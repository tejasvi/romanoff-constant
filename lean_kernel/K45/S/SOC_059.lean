import K45.G.L9_011
import K45.Orb.O118
import K45.Orb.O119
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_118 : c9_118.filterMap orbF = K45.Orb.orbs118 := by
  decide +kernel

theorem oc_119 : c9_119.filterMap orbF = K45.Orb.orbs119 := by
  decide +kernel

end K45.S
