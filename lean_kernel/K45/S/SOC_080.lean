import K45.G.L9_016
import K45.Orb.O160
import K45.Orb.O161
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_160 : c9_160.filterMap orbF = K45.Orb.orbs160 := by
  decide +kernel

theorem oc_161 : c9_161.filterMap orbF = K45.Orb.orbs161 := by
  decide +kernel

end K45.S
