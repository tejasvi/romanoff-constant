import K45.G.L9_002
import K45.Orb.O020
import K45.Orb.O021
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_020 : c9_020.filterMap orbF = K45.Orb.orbs020 := by
  decide +kernel

theorem oc_021 : c9_021.filterMap orbF = K45.Orb.orbs021 := by
  decide +kernel

end K45.S
