import K45.G.L9_003
import K45.Orb.O034
import K45.Orb.O035
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_034 : c9_034.filterMap orbF = K45.Orb.orbs034 := by
  decide +kernel

theorem oc_035 : c9_035.filterMap orbF = K45.Orb.orbs035 := by
  decide +kernel

end K45.S
