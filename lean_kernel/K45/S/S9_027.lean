import K45.G.L8_003
import K45.G.B9_006
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_108 : normK (prodK 120 c8_108 opts241) = b9_108 := by
  decide +kernel

theorem s9_109 : normK (prodK 120 c8_109 opts241) = b9_109 := by
  decide +kernel

theorem s9_110 : normK (prodK 120 c8_110 opts241) = b9_110 := by
  decide +kernel

theorem s9_111 : normK (prodK 120 c8_111 opts241) = b9_111 := by
  decide +kernel

end K45.S
