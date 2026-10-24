import K45.G.L9_002
import K45.Orb.O024
import K45.Orb.O025
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem oc_024 : c9_024.filterMap orbF = K45.Orb.orbs024 := by
  decide +kernel

theorem oc_025 : c9_025.filterMap orbF = K45.Orb.orbs025 := by
  decide +kernel

end K45.S
