import K45.G.L9_014
import K45.Orb.O140
import K45.Orb.O141
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_140 : c9_140.filterMap orbF = K45.Orb.orbs140 := by
  decide +kernel

theorem oc_141 : c9_141.filterMap orbF = K45.Orb.orbs141 := by
  decide +kernel

end K45.S
