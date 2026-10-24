import K45.G.L8_002
import K45.G.B9_003
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_060 : normK (prodK 120 c8_060 opts241) = b9_060 := by
  decide +kernel

theorem s9_061 : normK (prodK 120 c8_061 opts241) = b9_061 := by
  decide +kernel

theorem s9_062 : normK (prodK 120 c8_062 opts241) = b9_062 := by
  decide +kernel

theorem s9_063 : normK (prodK 120 c8_063 opts241) = b9_063 := by
  decide +kernel

end K45.S
