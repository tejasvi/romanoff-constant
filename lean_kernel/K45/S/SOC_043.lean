import K45.G.L9_008
import K45.Orb.O086
import K45.Orb.O087
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_086 : c9_086.filterMap orbF = K45.Orb.orbs086 := by
  decide +kernel

theorem oc_087 : c9_087.filterMap orbF = K45.Orb.orbs087 := by
  decide +kernel

end K45.S
