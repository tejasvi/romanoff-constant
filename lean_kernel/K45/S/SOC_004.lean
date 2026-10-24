import K45.G.L9_000
import K45.Orb.O008
import K45.Orb.O009
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_008 : c9_008.filterMap orbF = K45.Orb.orbs008 := by
  decide +kernel

theorem oc_009 : c9_009.filterMap orbF = K45.Orb.orbs009 := by
  decide +kernel

end K45.S
