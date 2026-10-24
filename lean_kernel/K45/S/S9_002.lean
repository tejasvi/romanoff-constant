import K45.G.L8_000
import K45.G.B9_000
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_008 : normK (prodK 120 c8_008 opts241) = b9_008 := by
  decide +kernel

theorem s9_009 : normK (prodK 120 c8_009 opts241) = b9_009 := by
  decide +kernel

theorem s9_010 : normK (prodK 120 c8_010 opts241) = b9_010 := by
  decide +kernel

theorem s9_011 : normK (prodK 120 c8_011 opts241) = b9_011 := by
  decide +kernel

end K45.S
