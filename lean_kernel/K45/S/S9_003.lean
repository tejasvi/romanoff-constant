import K45.G.L8_000
import K45.G.B9_000
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_012 : normK (prodK 120 c8_012 opts241) = b9_012 := by
  decide +kernel

theorem s9_013 : normK (prodK 120 c8_013 opts241) = b9_013 := by
  decide +kernel

theorem s9_014 : normK (prodK 120 c8_014 opts241) = b9_014 := by
  decide +kernel

theorem s9_015 : normK (prodK 120 c8_015 opts241) = b9_015 := by
  decide +kernel

end K45.S
