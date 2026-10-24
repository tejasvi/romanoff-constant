import K45.G.L9_014
import K45.Orb.O148
import K45.Orb.O149
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_148 : c9_148.filterMap orbF = K45.Orb.orbs148 := by
  decide +kernel

theorem oc_149 : c9_149.filterMap orbF = K45.Orb.orbs149 := by
  decide +kernel

end K45.S
