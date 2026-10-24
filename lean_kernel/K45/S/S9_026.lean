import K45.G.L8_003
import K45.G.B9_006
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_104 : normK (prodK 120 c8_104 opts241) = b9_104 := by
  decide +kernel

theorem s9_105 : normK (prodK 120 c8_105 opts241) = b9_105 := by
  decide +kernel

theorem s9_106 : normK (prodK 120 c8_106 opts241) = b9_106 := by
  decide +kernel

theorem s9_107 : normK (prodK 120 c8_107 opts241) = b9_107 := by
  decide +kernel

end K45.S
