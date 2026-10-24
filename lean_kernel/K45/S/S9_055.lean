import K45.G.L8_007
import K45.G.B9_013
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_220 : normK (prodK 120 c8_220 opts241) = b9_220 := by
  decide +kernel

theorem s9_221 : normK (prodK 120 c8_221 opts241) = b9_221 := by
  decide +kernel

end K45.S
