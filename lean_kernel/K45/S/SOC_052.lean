import K45.G.L9_010
import K45.Orb.O104
import K45.Orb.O105
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_104 : c9_104.filterMap orbF = K45.Orb.orbs104 := by
  decide +kernel

theorem oc_105 : c9_105.filterMap orbF = K45.Orb.orbs105 := by
  decide +kernel

end K45.S
