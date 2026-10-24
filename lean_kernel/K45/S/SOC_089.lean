import K45.G.L9_017
import K45.Orb.O178
import K45.Orb.O179
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_178 : c9_178.filterMap orbF = K45.Orb.orbs178 := by
  decide +kernel

theorem oc_179 : c9_179.filterMap orbF = K45.Orb.orbs179 := by
  decide +kernel

end K45.S
