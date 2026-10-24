import K45.G.L9_005
import K45.Orb.O050
import K45.Orb.O051
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_050 : c9_050.filterMap orbF = K45.Orb.orbs050 := by
  decide +kernel

theorem oc_051 : c9_051.filterMap orbF = K45.Orb.orbs051 := by
  decide +kernel

end K45.S
