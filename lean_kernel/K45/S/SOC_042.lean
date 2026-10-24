import K45.G.L9_008
import K45.Orb.O084
import K45.Orb.O085
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_084 : c9_084.filterMap orbF = K45.Orb.orbs084 := by
  decide +kernel

theorem oc_085 : c9_085.filterMap orbF = K45.Orb.orbs085 := by
  decide +kernel

end K45.S
