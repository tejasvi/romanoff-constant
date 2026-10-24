import K45.G.L9_004
import K45.Orb.O048
import K45.Orb.O049
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_048 : c9_048.filterMap orbF = K45.Orb.orbs048 := by
  decide +kernel

theorem oc_049 : c9_049.filterMap orbF = K45.Orb.orbs049 := by
  decide +kernel

end K45.S
