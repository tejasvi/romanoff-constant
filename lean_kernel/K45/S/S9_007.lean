import K45.G.L8_001
import K45.G.B9_001
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_028 : normK (prodK 120 c8_028 opts241) = b9_028 := by
  decide +kernel

theorem s9_029 : normK (prodK 120 c8_029 opts241) = b9_029 := by
  decide +kernel

theorem s9_030 : normK (prodK 120 c8_030 opts241) = b9_030 := by
  decide +kernel

theorem s9_031 : normK (prodK 120 c8_031 opts241) = b9_031 := by
  decide +kernel

end K45.S
