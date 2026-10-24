import K45.G.L9_001
import K45.Orb.O012
import K45.Orb.O013
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_012 : c9_012.filterMap orbF = K45.Orb.orbs012 := by
  decide +kernel

theorem oc_013 : c9_013.filterMap orbF = K45.Orb.orbs013 := by
  decide +kernel

end K45.S
