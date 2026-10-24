import K45.G.L9_017
import K45.Orb.O172
import K45.Orb.O173
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_172 : c9_172.filterMap orbF = K45.Orb.orbs172 := by
  decide +kernel

theorem oc_173 : c9_173.filterMap orbF = K45.Orb.orbs173 := by
  decide +kernel

end K45.S
