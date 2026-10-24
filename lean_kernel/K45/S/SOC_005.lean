import K45.G.L9_001
import K45.Orb.O010
import K45.Orb.O011
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_010 : c9_010.filterMap orbF = K45.Orb.orbs010 := by
  decide +kernel

theorem oc_011 : c9_011.filterMap orbF = K45.Orb.orbs011 := by
  decide +kernel

end K45.S
