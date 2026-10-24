import K45G.BG
import K45G.LG
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45G

open R45 K45

theorem sgm : mergeRuns BGs = LG := by
  decide +kernel

theorem pG : strictPos LG = true := by
  decide +kernel

end K45G
