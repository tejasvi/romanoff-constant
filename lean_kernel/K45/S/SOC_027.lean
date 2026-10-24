import K45.G.L9_005
import K45.Orb.O054
import K45.Orb.O055
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_054 : c9_054.filterMap orbF = K45.Orb.orbs054 := by
  decide +kernel

theorem oc_055 : c9_055.filterMap orbF = K45.Orb.orbs055 := by
  decide +kernel

end K45.S
