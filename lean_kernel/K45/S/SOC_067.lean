import K45.G.L9_013
import K45.Orb.O134
import K45.Orb.O135
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_134 : c9_134.filterMap orbF = K45.Orb.orbs134 := by
  decide +kernel

theorem oc_135 : c9_135.filterMap orbF = K45.Orb.orbs135 := by
  decide +kernel

end K45.S
