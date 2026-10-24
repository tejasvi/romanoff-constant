import K45.G.L9_015
import K45.Orb.O156
import K45.Orb.O157
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_156 : c9_156.filterMap orbF = K45.Orb.orbs156 := by
  decide +kernel

theorem oc_157 : c9_157.filterMap orbF = K45.Orb.orbs157 := by
  decide +kernel

end K45.S
