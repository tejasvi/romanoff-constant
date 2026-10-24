import K45.G.Lsmall
import K45.G.B8
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s8_006 : normK (prodK 120 c7_006 opts41) = b8_006 := by
  decide +kernel

theorem s8_007 : normK (prodK 120 c7_007 opts41) = b8_007 := by
  decide +kernel

theorem s8_008 : normK (prodK 120 c7_008 opts41) = b8_008 := by
  decide +kernel

end K45.S
