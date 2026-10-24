import K45.G.L8_006
import K45.G.B9_010
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_168 : normK (prodK 120 c8_168 opts241) = b9_168 := by
  decide +kernel

theorem s9_169 : normK (prodK 120 c8_169 opts241) = b9_169 := by
  decide +kernel

theorem s9_170 : normK (prodK 120 c8_170 opts241) = b9_170 := by
  decide +kernel

theorem s9_171 : normK (prodK 120 c8_171 opts241) = b9_171 := by
  decide +kernel

end K45.S
