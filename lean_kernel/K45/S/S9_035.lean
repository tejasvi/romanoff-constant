import K45.G.L8_005
import K45.G.B9_008
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_140 : normK (prodK 120 c8_140 opts241) = b9_140 := by
  decide +kernel

theorem s9_141 : normK (prodK 120 c8_141 opts241) = b9_141 := by
  decide +kernel

theorem s9_142 : normK (prodK 120 c8_142 opts241) = b9_142 := by
  decide +kernel

theorem s9_143 : normK (prodK 120 c8_143 opts241) = b9_143 := by
  decide +kernel

end K45.S
