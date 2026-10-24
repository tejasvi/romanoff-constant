import K45.G.L8_004
import K45.G.B9_007
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_120 : normK (prodK 120 c8_120 opts241) = b9_120 := by
  decide +kernel

theorem s9_121 : normK (prodK 120 c8_121 opts241) = b9_121 := by
  decide +kernel

theorem s9_122 : normK (prodK 120 c8_122 opts241) = b9_122 := by
  decide +kernel

theorem s9_123 : normK (prodK 120 c8_123 opts241) = b9_123 := by
  decide +kernel

end K45.S
