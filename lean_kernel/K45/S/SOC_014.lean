import K45.G.L9_002
import K45.Orb.O028
import K45.Orb.O029
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_028 : c9_028.filterMap orbF = K45.Orb.orbs028 := by
  decide +kernel

theorem oc_029 : c9_029.filterMap orbF = K45.Orb.orbs029 := by
  decide +kernel

end K45.S
