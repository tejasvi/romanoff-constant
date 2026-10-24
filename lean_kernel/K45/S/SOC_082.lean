import K45.G.L9_016
import K45.Orb.O164
import K45.Orb.O165
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_164 : c9_164.filterMap orbF = K45.Orb.orbs164 := by
  decide +kernel

theorem oc_165 : c9_165.filterMap orbF = K45.Orb.orbs165 := by
  decide +kernel

end K45.S
