import K45.G.M9_000
import K45.G.M9_001
import K45.G.M9_002
import K45.G.M9_003
import K45.G.M9_004
import K45.G.M9_005
import K45.G.M9_006
import K45.G.M9_007
import K45.G.M9_008
import K45.G.M9_009
import K45.G.M9_010
import K45.G.M9_011
import K45.G.M9_012
import K45.G.M9_013
import K45.G.L9
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem m9all : mergeRuns [m9_000, m9_001, m9_002, m9_003, m9_004, m9_005, m9_006, m9_007, m9_008, m9_009, m9_010, m9_011, m9_012, m9_013] = L9 := by
  decide +kernel

theorem p9 : strictPos L9 = true := by
  decide +kernel

end K45.S
