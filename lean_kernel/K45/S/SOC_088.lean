import K45.G.L9_017
import K45.Orb.O176
import K45.Orb.O177
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_176 : c9_176.filterMap orbF = K45.Orb.orbs176 := by
  decide +kernel

theorem oc_177 : c9_177.filterMap orbF = K45.Orb.orbs177 := by
  decide +kernel

end K45.S
