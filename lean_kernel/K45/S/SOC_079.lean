import K45.G.L9_015
import K45.Orb.O158
import K45.Orb.O159
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_158 : c9_158.filterMap orbF = K45.Orb.orbs158 := by
  decide +kernel

theorem oc_159 : c9_159.filterMap orbF = K45.Orb.orbs159 := by
  decide +kernel

end K45.S
