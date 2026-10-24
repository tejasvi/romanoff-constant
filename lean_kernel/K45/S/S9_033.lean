import K45.G.L8_004
import K45.G.B9_008
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_132 : normK (prodK 120 c8_132 opts241) = b9_132 := by
  decide +kernel

theorem s9_133 : normK (prodK 120 c8_133 opts241) = b9_133 := by
  decide +kernel

theorem s9_134 : normK (prodK 120 c8_134 opts241) = b9_134 := by
  decide +kernel

theorem s9_135 : normK (prodK 120 c8_135 opts241) = b9_135 := by
  decide +kernel

end K45.S
