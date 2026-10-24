import K45.G.L8_000
import K45.G.B9_001
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s9_024 : normK (prodK 120 c8_024 opts241) = b9_024 := by
  decide +kernel

theorem s9_025 : normK (prodK 120 c8_025 opts241) = b9_025 := by
  decide +kernel

theorem s9_026 : normK (prodK 120 c8_026 opts241) = b9_026 := by
  decide +kernel

theorem s9_027 : normK (prodK 120 c8_027 opts241) = b9_027 := by
  decide +kernel

end K45.S
