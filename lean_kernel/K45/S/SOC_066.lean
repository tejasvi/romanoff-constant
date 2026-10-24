import K45.G.L9_013
import K45.Orb.O132
import K45.Orb.O133
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_132 : c9_132.filterMap orbF = K45.Orb.orbs132 := by
  decide +kernel

theorem oc_133 : c9_133.filterMap orbF = K45.Orb.orbs133 := by
  decide +kernel

end K45.S
