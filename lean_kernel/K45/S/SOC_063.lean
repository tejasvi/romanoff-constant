import K45.G.L9_012
import K45.Orb.O126
import K45.Orb.O127
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_126 : c9_126.filterMap orbF = K45.Orb.orbs126 := by
  decide +kernel

theorem oc_127 : c9_127.filterMap orbF = K45.Orb.orbs127 := by
  decide +kernel

end K45.S
