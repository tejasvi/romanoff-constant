import K45.G.L8_001
import K45.G.B9_002
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_040 : normK (prodK 120 c8_040 opts241) = b9_040 := by
  decide +kernel

theorem s9_041 : normK (prodK 120 c8_041 opts241) = b9_041 := by
  decide +kernel

theorem s9_042 : normK (prodK 120 c8_042 opts241) = b9_042 := by
  decide +kernel

theorem s9_043 : normK (prodK 120 c8_043 opts241) = b9_043 := by
  decide +kernel

end K45.S
