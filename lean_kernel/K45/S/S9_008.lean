import K45.G.L8_001
import K45.G.B9_002
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_032 : normK (prodK 120 c8_032 opts241) = b9_032 := by
  decide +kernel

theorem s9_033 : normK (prodK 120 c8_033 opts241) = b9_033 := by
  decide +kernel

theorem s9_034 : normK (prodK 120 c8_034 opts241) = b9_034 := by
  decide +kernel

theorem s9_035 : normK (prodK 120 c8_035 opts241) = b9_035 := by
  decide +kernel

end K45.S
