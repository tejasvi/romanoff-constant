import K45.G.L8_000
import K45.G.B9_000
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_004 : normK (prodK 120 c8_004 opts241) = b9_004 := by
  decide +kernel

theorem s9_005 : normK (prodK 120 c8_005 opts241) = b9_005 := by
  decide +kernel

theorem s9_006 : normK (prodK 120 c8_006 opts241) = b9_006 := by
  decide +kernel

theorem s9_007 : normK (prodK 120 c8_007 opts241) = b9_007 := by
  decide +kernel

end K45.S
