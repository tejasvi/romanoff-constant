import K45.G.L9_004
import K45.Orb.O046
import K45.Orb.O047
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_046 : c9_046.filterMap orbF = K45.Orb.orbs046 := by
  decide +kernel

theorem oc_047 : c9_047.filterMap orbF = K45.Orb.orbs047 := by
  decide +kernel

end K45.S
