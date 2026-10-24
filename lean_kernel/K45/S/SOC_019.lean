import K45.G.L9_003
import K45.Orb.O038
import K45.Orb.O039
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_038 : c9_038.filterMap orbF = K45.Orb.orbs038 := by
  decide +kernel

theorem oc_039 : c9_039.filterMap orbF = K45.Orb.orbs039 := by
  decide +kernel

end K45.S
