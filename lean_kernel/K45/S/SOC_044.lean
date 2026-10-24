import K45.G.L9_008
import K45.Orb.O088
import K45.Orb.O089
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_088 : c9_088.filterMap orbF = K45.Orb.orbs088 := by
  decide +kernel

theorem oc_089 : c9_089.filterMap orbF = K45.Orb.orbs089 := by
  decide +kernel

end K45.S
