import K45.G.L9_000
import K45.Orb.O004
import K45.Orb.O005
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_004 : c9_004.filterMap orbF = K45.Orb.orbs004 := by
  decide +kernel

theorem oc_005 : c9_005.filterMap orbF = K45.Orb.orbs005 := by
  decide +kernel

end K45.S
