import K45.G.L9_014
import K45.Orb.O146
import K45.Orb.O147
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_146 : c9_146.filterMap orbF = K45.Orb.orbs146 := by
  decide +kernel

theorem oc_147 : c9_147.filterMap orbF = K45.Orb.orbs147 := by
  decide +kernel

end K45.S
