import K45.G.L8_000
import K45.G.B9_000
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_000 : normK (prodK 120 c8_000 opts241) = b9_000 := by
  decide +kernel

theorem s9_001 : normK (prodK 120 c8_001 opts241) = b9_001 := by
  decide +kernel

theorem s9_002 : normK (prodK 120 c8_002 opts241) = b9_002 := by
  decide +kernel

theorem s9_003 : normK (prodK 120 c8_003 opts241) = b9_003 := by
  decide +kernel

end K45.S
