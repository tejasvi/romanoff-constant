import K45.G.L9_009
import K45.Orb.O092
import K45.Orb.O093
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_092 : c9_092.filterMap orbF = K45.Orb.orbs092 := by
  decide +kernel

theorem oc_093 : c9_093.filterMap orbF = K45.Orb.orbs093 := by
  decide +kernel

end K45.S
