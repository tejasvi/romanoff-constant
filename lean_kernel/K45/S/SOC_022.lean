import K45.G.L9_004
import K45.Orb.O044
import K45.Orb.O045
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_044 : c9_044.filterMap orbF = K45.Orb.orbs044 := by
  decide +kernel

theorem oc_045 : c9_045.filterMap orbF = K45.Orb.orbs045 := by
  decide +kernel

end K45.S
