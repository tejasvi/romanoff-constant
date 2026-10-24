import K45.G.L9_011
import K45.Orb.O112
import K45.Orb.O113
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_112 : c9_112.filterMap orbF = K45.Orb.orbs112 := by
  decide +kernel

theorem oc_113 : c9_113.filterMap orbF = K45.Orb.orbs113 := by
  decide +kernel

end K45.S
