import K45.G.L9_015
import K45.Orb.O150
import K45.Orb.O151
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_150 : c9_150.filterMap orbF = K45.Orb.orbs150 := by
  decide +kernel

theorem oc_151 : c9_151.filterMap orbF = K45.Orb.orbs151 := by
  decide +kernel

end K45.S
