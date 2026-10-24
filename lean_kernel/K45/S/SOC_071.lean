import K45.G.L9_014
import K45.Orb.O142
import K45.Orb.O143
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_142 : c9_142.filterMap orbF = K45.Orb.orbs142 := by
  decide +kernel

theorem oc_143 : c9_143.filterMap orbF = K45.Orb.orbs143 := by
  decide +kernel

end K45.S
