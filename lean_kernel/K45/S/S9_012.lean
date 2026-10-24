import K45.G.L8_001
import K45.G.B9_003
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_048 : normK (prodK 120 c8_048 opts241) = b9_048 := by
  decide +kernel

theorem s9_049 : normK (prodK 120 c8_049 opts241) = b9_049 := by
  decide +kernel

theorem s9_050 : normK (prodK 120 c8_050 opts241) = b9_050 := by
  decide +kernel

theorem s9_051 : normK (prodK 120 c8_051 opts241) = b9_051 := by
  decide +kernel

end K45.S
