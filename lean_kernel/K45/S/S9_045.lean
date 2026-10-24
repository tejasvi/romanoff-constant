import K45.G.L8_006
import K45.G.B9_011
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_180 : normK (prodK 120 c8_180 opts241) = b9_180 := by
  decide +kernel

theorem s9_181 : normK (prodK 120 c8_181 opts241) = b9_181 := by
  decide +kernel

theorem s9_182 : normK (prodK 120 c8_182 opts241) = b9_182 := by
  decide +kernel

theorem s9_183 : normK (prodK 120 c8_183 opts241) = b9_183 := by
  decide +kernel

end K45.S
