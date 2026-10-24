import K45.G.Lsmall
import K45.G.B8
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s8_000 : normK (prodK 120 c7_000 opts41) = b8_000 := by
  decide +kernel

theorem s8_001 : normK (prodK 120 c7_001 opts41) = b8_001 := by
  decide +kernel

theorem s8_002 : normK (prodK 120 c7_002 opts41) = b8_002 := by
  decide +kernel

end K45.S
