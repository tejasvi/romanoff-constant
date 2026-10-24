import K45.G.L9_004
import K45.Orb.O040
import K45.Orb.O041
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_040 : c9_040.filterMap orbF = K45.Orb.orbs040 := by
  decide +kernel

theorem oc_041 : c9_041.filterMap orbF = K45.Orb.orbs041 := by
  decide +kernel

end K45.S
