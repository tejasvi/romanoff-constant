import K45.G.L9_018
import K45.Orb.O180
import K45.Orb.O181
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_180 : c9_180.filterMap orbF = K45.Orb.orbs180 := by
  decide +kernel

theorem oc_181 : c9_181.filterMap orbF = K45.Orb.orbs181 := by
  decide +kernel

end K45.S
