import K45.G.L9_006
import K45.Orb.O064
import K45.Orb.O065
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_064 : c9_064.filterMap orbF = K45.Orb.orbs064 := by
  decide +kernel

theorem oc_065 : c9_065.filterMap orbF = K45.Orb.orbs065 := by
  decide +kernel

end K45.S
