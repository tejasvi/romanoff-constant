import K45.G.Lsmall
import K45.G.B8
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s8_015 : normK (prodK 120 c7_015 opts41) = b8_015 := by
  decide +kernel

theorem s8_016 : normK (prodK 120 c7_016 opts41) = b8_016 := by
  decide +kernel

theorem s8_017 : normK (prodK 120 c7_017 opts41) = b8_017 := by
  decide +kernel

end K45.S
