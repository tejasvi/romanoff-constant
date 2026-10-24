import K45.G.L9_009
import K45.Orb.O090
import K45.Orb.O091
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_090 : c9_090.filterMap orbF = K45.Orb.orbs090 := by
  decide +kernel

theorem oc_091 : c9_091.filterMap orbF = K45.Orb.orbs091 := by
  decide +kernel

end K45.S
