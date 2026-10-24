import K45.G.L8_000
import K45.G.B9_001
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_016 : normK (prodK 120 c8_016 opts241) = b9_016 := by
  decide +kernel

theorem s9_017 : normK (prodK 120 c8_017 opts241) = b9_017 := by
  decide +kernel

theorem s9_018 : normK (prodK 120 c8_018 opts241) = b9_018 := by
  decide +kernel

theorem s9_019 : normK (prodK 120 c8_019 opts241) = b9_019 := by
  decide +kernel

end K45.S
