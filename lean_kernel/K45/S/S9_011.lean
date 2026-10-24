import K45.G.L8_001
import K45.G.B9_002
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_044 : normK (prodK 120 c8_044 opts241) = b9_044 := by
  decide +kernel

theorem s9_045 : normK (prodK 120 c8_045 opts241) = b9_045 := by
  decide +kernel

theorem s9_046 : normK (prodK 120 c8_046 opts241) = b9_046 := by
  decide +kernel

theorem s9_047 : normK (prodK 120 c8_047 opts241) = b9_047 := by
  decide +kernel

end K45.S
