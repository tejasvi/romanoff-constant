import K45.G.L9_007
import K45.Orb.O072
import K45.Orb.O073
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_072 : c9_072.filterMap orbF = K45.Orb.orbs072 := by
  decide +kernel

theorem oc_073 : c9_073.filterMap orbF = K45.Orb.orbs073 := by
  decide +kernel

end K45.S
