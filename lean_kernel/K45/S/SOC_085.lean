import K45.G.L9_017
import K45.Orb.O170
import K45.Orb.O171
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_170 : c9_170.filterMap orbF = K45.Orb.orbs170 := by
  decide +kernel

theorem oc_171 : c9_171.filterMap orbF = K45.Orb.orbs171 := by
  decide +kernel

end K45.S
