import K45.G.L8_007
import K45.G.B9_013
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_208 : normK (prodK 120 c8_208 opts241) = b9_208 := by
  decide +kernel

theorem s9_209 : normK (prodK 120 c8_209 opts241) = b9_209 := by
  decide +kernel

theorem s9_210 : normK (prodK 120 c8_210 opts241) = b9_210 := by
  decide +kernel

theorem s9_211 : normK (prodK 120 c8_211 opts241) = b9_211 := by
  decide +kernel

end K45.S
