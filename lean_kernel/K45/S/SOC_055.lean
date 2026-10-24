import K45.G.L9_011
import K45.Orb.O110
import K45.Orb.O111
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_110 : c9_110.filterMap orbF = K45.Orb.orbs110 := by
  decide +kernel

theorem oc_111 : c9_111.filterMap orbF = K45.Orb.orbs111 := by
  decide +kernel

end K45.S
