import K45.G.L8_007
import K45.G.B9_013
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_212 : normK (prodK 120 c8_212 opts241) = b9_212 := by
  decide +kernel

theorem s9_213 : normK (prodK 120 c8_213 opts241) = b9_213 := by
  decide +kernel

theorem s9_214 : normK (prodK 120 c8_214 opts241) = b9_214 := by
  decide +kernel

theorem s9_215 : normK (prodK 120 c8_215 opts241) = b9_215 := by
  decide +kernel

end K45.S
