import K45.G.L8_007
import K45.G.B9_012
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_204 : normK (prodK 120 c8_204 opts241) = b9_204 := by
  decide +kernel

theorem s9_205 : normK (prodK 120 c8_205 opts241) = b9_205 := by
  decide +kernel

theorem s9_206 : normK (prodK 120 c8_206 opts241) = b9_206 := by
  decide +kernel

theorem s9_207 : normK (prodK 120 c8_207 opts241) = b9_207 := by
  decide +kernel

end K45.S
