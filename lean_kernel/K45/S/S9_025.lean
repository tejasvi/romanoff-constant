import K45.G.L8_003
import K45.G.B9_006
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_100 : normK (prodK 120 c8_100 opts241) = b9_100 := by
  decide +kernel

theorem s9_101 : normK (prodK 120 c8_101 opts241) = b9_101 := by
  decide +kernel

theorem s9_102 : normK (prodK 120 c8_102 opts241) = b9_102 := by
  decide +kernel

theorem s9_103 : normK (prodK 120 c8_103 opts241) = b9_103 := by
  decide +kernel

end K45.S
