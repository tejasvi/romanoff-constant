import K45.G.Lsmall
import K45.G.B8
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s8_012 : normK (prodK 120 c7_012 opts41) = b8_012 := by
  decide +kernel

theorem s8_013 : normK (prodK 120 c7_013 opts41) = b8_013 := by
  decide +kernel

theorem s8_014 : normK (prodK 120 c7_014 opts41) = b8_014 := by
  decide +kernel

end K45.S
