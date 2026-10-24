import K45.G.L9_001
import K45.Orb.O014
import K45.Orb.O015
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_014 : c9_014.filterMap orbF = K45.Orb.orbs014 := by
  decide +kernel

theorem oc_015 : c9_015.filterMap orbF = K45.Orb.orbs015 := by
  decide +kernel

end K45.S
