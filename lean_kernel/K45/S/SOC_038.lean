import K45.G.L9_007
import K45.Orb.O076
import K45.Orb.O077
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_076 : c9_076.filterMap orbF = K45.Orb.orbs076 := by
  decide +kernel

theorem oc_077 : c9_077.filterMap orbF = K45.Orb.orbs077 := by
  decide +kernel

end K45.S
