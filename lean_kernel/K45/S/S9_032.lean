import K45.G.L8_004
import K45.G.B9_008
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_128 : normK (prodK 120 c8_128 opts241) = b9_128 := by
  decide +kernel

theorem s9_129 : normK (prodK 120 c8_129 opts241) = b9_129 := by
  decide +kernel

theorem s9_130 : normK (prodK 120 c8_130 opts241) = b9_130 := by
  decide +kernel

theorem s9_131 : normK (prodK 120 c8_131 opts241) = b9_131 := by
  decide +kernel

end K45.S
