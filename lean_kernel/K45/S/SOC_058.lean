import K45.G.L9_011
import K45.Orb.O116
import K45.Orb.O117
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_116 : c9_116.filterMap orbF = K45.Orb.orbs116 := by
  decide +kernel

theorem oc_117 : c9_117.filterMap orbF = K45.Orb.orbs117 := by
  decide +kernel

end K45.S
