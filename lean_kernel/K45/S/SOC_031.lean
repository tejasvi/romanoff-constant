import K45.G.L9_006
import K45.Orb.O062
import K45.Orb.O063
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_062 : c9_062.filterMap orbF = K45.Orb.orbs062 := by
  decide +kernel

theorem oc_063 : c9_063.filterMap orbF = K45.Orb.orbs063 := by
  decide +kernel

end K45.S
