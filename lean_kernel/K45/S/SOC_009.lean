import K45.G.L9_001
import K45.Orb.O018
import K45.Orb.O019
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_018 : c9_018.filterMap orbF = K45.Orb.orbs018 := by
  decide +kernel

theorem oc_019 : c9_019.filterMap orbF = K45.Orb.orbs019 := by
  decide +kernel

end K45.S
