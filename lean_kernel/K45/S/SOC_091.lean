import K45.G.L9_018
import K45.Orb.O182
import K45.Orb.O183
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_182 : c9_182.filterMap orbF = K45.Orb.orbs182 := by
  decide +kernel

theorem oc_183 : c9_183.filterMap orbF = K45.Orb.orbs183 := by
  decide +kernel

end K45.S
