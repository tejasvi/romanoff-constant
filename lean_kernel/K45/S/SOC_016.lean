import K45.G.L9_003
import K45.Orb.O032
import K45.Orb.O033
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_032 : c9_032.filterMap orbF = K45.Orb.orbs032 := by
  decide +kernel

theorem oc_033 : c9_033.filterMap orbF = K45.Orb.orbs033 := by
  decide +kernel

end K45.S
