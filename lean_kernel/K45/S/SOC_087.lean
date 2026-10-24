import K45.G.L9_017
import K45.Orb.O174
import K45.Orb.O175
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_174 : c9_174.filterMap orbF = K45.Orb.orbs174 := by
  decide +kernel

theorem oc_175 : c9_175.filterMap orbF = K45.Orb.orbs175 := by
  decide +kernel

end K45.S
