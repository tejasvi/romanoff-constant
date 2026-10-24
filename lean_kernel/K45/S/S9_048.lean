import K45.G.L8_006
import K45.G.B9_012
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_192 : normK (prodK 120 c8_192 opts241) = b9_192 := by
  decide +kernel

theorem s9_193 : normK (prodK 120 c8_193 opts241) = b9_193 := by
  decide +kernel

theorem s9_194 : normK (prodK 120 c8_194 opts241) = b9_194 := by
  decide +kernel

theorem s9_195 : normK (prodK 120 c8_195 opts241) = b9_195 := by
  decide +kernel

end K45.S
