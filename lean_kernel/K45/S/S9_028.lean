import K45.G.L8_004
import K45.G.B9_007
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_112 : normK (prodK 120 c8_112 opts241) = b9_112 := by
  decide +kernel

theorem s9_113 : normK (prodK 120 c8_113 opts241) = b9_113 := by
  decide +kernel

theorem s9_114 : normK (prodK 120 c8_114 opts241) = b9_114 := by
  decide +kernel

theorem s9_115 : normK (prodK 120 c8_115 opts241) = b9_115 := by
  decide +kernel

end K45.S
