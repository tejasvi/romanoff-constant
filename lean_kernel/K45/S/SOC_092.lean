import K45.G.L9_018
import K45.Orb.O184
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_184 : c9_184.filterMap orbF = K45.Orb.orbs184 := by
  decide +kernel

end K45.S
