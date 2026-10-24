import K45.G.L9_002
import K45.Orb.O026
import K45.Orb.O027
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_026 : c9_026.filterMap orbF = K45.Orb.orbs026 := by
  decide +kernel

theorem oc_027 : c9_027.filterMap orbF = K45.Orb.orbs027 := by
  decide +kernel

end K45.S
