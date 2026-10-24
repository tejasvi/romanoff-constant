import K45.G.L9_014
import K45.Orb.O144
import K45.Orb.O145
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_144 : c9_144.filterMap orbF = K45.Orb.orbs144 := by
  decide +kernel

theorem oc_145 : c9_145.filterMap orbF = K45.Orb.orbs145 := by
  decide +kernel

end K45.S
