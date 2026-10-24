import K45.G.L8_007
import K45.G.B9_012
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_200 : normK (prodK 120 c8_200 opts241) = b9_200 := by
  decide +kernel

theorem s9_201 : normK (prodK 120 c8_201 opts241) = b9_201 := by
  decide +kernel

theorem s9_202 : normK (prodK 120 c8_202 opts241) = b9_202 := by
  decide +kernel

theorem s9_203 : normK (prodK 120 c8_203 opts241) = b9_203 := by
  decide +kernel

end K45.S
