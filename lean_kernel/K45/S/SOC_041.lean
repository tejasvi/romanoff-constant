import K45.G.L9_008
import K45.Orb.O082
import K45.Orb.O083
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_082 : c9_082.filterMap orbF = K45.Orb.orbs082 := by
  decide +kernel

theorem oc_083 : c9_083.filterMap orbF = K45.Orb.orbs083 := by
  decide +kernel

end K45.S
