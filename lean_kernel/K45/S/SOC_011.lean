import K45.G.L9_002
import K45.Orb.O022
import K45.Orb.O023
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_022 : c9_022.filterMap orbF = K45.Orb.orbs022 := by
  decide +kernel

theorem oc_023 : c9_023.filterMap orbF = K45.Orb.orbs023 := by
  decide +kernel

end K45.S
