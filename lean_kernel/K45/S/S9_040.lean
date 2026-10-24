import K45.G.L8_005
import K45.G.B9_010
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_160 : normK (prodK 120 c8_160 opts241) = b9_160 := by
  decide +kernel

theorem s9_161 : normK (prodK 120 c8_161 opts241) = b9_161 := by
  decide +kernel

theorem s9_162 : normK (prodK 120 c8_162 opts241) = b9_162 := by
  decide +kernel

theorem s9_163 : normK (prodK 120 c8_163 opts241) = b9_163 := by
  decide +kernel

end K45.S
