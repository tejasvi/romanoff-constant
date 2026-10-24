import K45.G.Lsmall
import K45.G.B8
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s8_009 : normK (prodK 120 c7_009 opts41) = b8_009 := by
  decide +kernel

theorem s8_010 : normK (prodK 120 c7_010 opts41) = b8_010 := by
  decide +kernel

theorem s8_011 : normK (prodK 120 c7_011 opts41) = b8_011 := by
  decide +kernel

end K45.S
