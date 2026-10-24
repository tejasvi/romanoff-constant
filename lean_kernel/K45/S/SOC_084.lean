import K45.G.L9_016
import K45.Orb.O168
import K45.Orb.O169
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_168 : c9_168.filterMap orbF = K45.Orb.orbs168 := by
  decide +kernel

theorem oc_169 : c9_169.filterMap orbF = K45.Orb.orbs169 := by
  decide +kernel

end K45.S
