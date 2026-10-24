import K45.G.L8_002
import K45.G.B9_005
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_080 : normK (prodK 120 c8_080 opts241) = b9_080 := by
  decide +kernel

theorem s9_081 : normK (prodK 120 c8_081 opts241) = b9_081 := by
  decide +kernel

theorem s9_082 : normK (prodK 120 c8_082 opts241) = b9_082 := by
  decide +kernel

theorem s9_083 : normK (prodK 120 c8_083 opts241) = b9_083 := by
  decide +kernel

end K45.S
