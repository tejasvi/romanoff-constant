import K45.G.Lsmall
import K45.G.B8
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s8_003 : normK (prodK 120 c7_003 opts41) = b8_003 := by
  decide +kernel

theorem s8_004 : normK (prodK 120 c7_004 opts41) = b8_004 := by
  decide +kernel

theorem s8_005 : normK (prodK 120 c7_005 opts41) = b8_005 := by
  decide +kernel

end K45.S
