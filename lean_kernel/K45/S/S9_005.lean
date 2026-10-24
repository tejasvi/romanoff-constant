import K45.G.L8_000
import K45.G.B9_001
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_020 : normK (prodK 120 c8_020 opts241) = b9_020 := by
  decide +kernel

theorem s9_021 : normK (prodK 120 c8_021 opts241) = b9_021 := by
  decide +kernel

theorem s9_022 : normK (prodK 120 c8_022 opts241) = b9_022 := by
  decide +kernel

theorem s9_023 : normK (prodK 120 c8_023 opts241) = b9_023 := by
  decide +kernel

end K45.S
