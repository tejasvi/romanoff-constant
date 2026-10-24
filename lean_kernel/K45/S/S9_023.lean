import K45.G.L8_003
import K45.G.B9_005
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_092 : normK (prodK 120 c8_092 opts241) = b9_092 := by
  decide +kernel

theorem s9_093 : normK (prodK 120 c8_093 opts241) = b9_093 := by
  decide +kernel

theorem s9_094 : normK (prodK 120 c8_094 opts241) = b9_094 := by
  decide +kernel

theorem s9_095 : normK (prodK 120 c8_095 opts241) = b9_095 := by
  decide +kernel

end K45.S
