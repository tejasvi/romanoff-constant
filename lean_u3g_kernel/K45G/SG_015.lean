import K45.G.Lsmall
import K45.G.Opts
import K45.Defs
import K45G.BG

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45G

open R45 K45 K45.G

theorem sg_015 : normK (prodK 120 c7_015 opts241) = bg_015 := by
  decide +kernel

end K45G
