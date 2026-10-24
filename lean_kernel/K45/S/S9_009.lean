import K45.G.L8_001
import K45.G.B9_002
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_036 : normK (prodK 120 c8_036 opts241) = b9_036 := by
  decide +kernel

theorem s9_037 : normK (prodK 120 c8_037 opts241) = b9_037 := by
  decide +kernel

theorem s9_038 : normK (prodK 120 c8_038 opts241) = b9_038 := by
  decide +kernel

theorem s9_039 : normK (prodK 120 c8_039 opts241) = b9_039 := by
  decide +kernel

end K45.S
