import K45.G.L9_007
import K45.Orb.O078
import K45.Orb.O079
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_078 : c9_078.filterMap orbF = K45.Orb.orbs078 := by
  decide +kernel

theorem oc_079 : c9_079.filterMap orbF = K45.Orb.orbs079 := by
  decide +kernel

end K45.S
