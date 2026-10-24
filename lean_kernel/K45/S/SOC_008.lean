import K45.G.L9_001
import K45.Orb.O016
import K45.Orb.O017
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_016 : c9_016.filterMap orbF = K45.Orb.orbs016 := by
  decide +kernel

theorem oc_017 : c9_017.filterMap orbF = K45.Orb.orbs017 := by
  decide +kernel

end K45.S
