import K45.G.L9_009
import K45.Orb.O096
import K45.Orb.O097
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_096 : c9_096.filterMap orbF = K45.Orb.orbs096 := by
  decide +kernel

theorem oc_097 : c9_097.filterMap orbF = K45.Orb.orbs097 := by
  decide +kernel

end K45.S
