import K45.G.L9_016
import K45.Orb.O166
import K45.Orb.O167
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_166 : c9_166.filterMap orbF = K45.Orb.orbs166 := by
  decide +kernel

theorem oc_167 : c9_167.filterMap orbF = K45.Orb.orbs167 := by
  decide +kernel

end K45.S
