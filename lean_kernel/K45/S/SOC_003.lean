import K45.G.L9_000
import K45.Orb.O006
import K45.Orb.O007
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_006 : c9_006.filterMap orbF = K45.Orb.orbs006 := by
  decide +kernel

theorem oc_007 : c9_007.filterMap orbF = K45.Orb.orbs007 := by
  decide +kernel

end K45.S
