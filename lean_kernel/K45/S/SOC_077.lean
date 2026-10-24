import K45.G.L9_015
import K45.Orb.O154
import K45.Orb.O155
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_154 : c9_154.filterMap orbF = K45.Orb.orbs154 := by
  decide +kernel

theorem oc_155 : c9_155.filterMap orbF = K45.Orb.orbs155 := by
  decide +kernel

end K45.S
