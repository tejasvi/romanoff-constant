import K45.G.Lsmall
import K45.G.Opts
import K45.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem s1 : normK (prodK 120 [(0, 1)] opts3) = L1 := by
  decide +kernel

theorem p1 : strictPos L1 = true := by
  decide +kernel

theorem s2 : normK (prodK 120 L1 opts5) = L2 := by
  decide +kernel

theorem p2 : strictPos L2 = true := by
  decide +kernel

theorem s3 : normK (prodK 120 L2 opts7) = L3 := by
  decide +kernel

theorem p3 : strictPos L3 = true := by
  decide +kernel

theorem s4 : normK (prodK 120 L3 opts11) = L4 := by
  decide +kernel

theorem p4 : strictPos L4 = true := by
  decide +kernel

theorem s5 : normK (prodK 120 L4 opts13) = L5 := by
  decide +kernel

theorem p5 : strictPos L5 = true := by
  decide +kernel

theorem s6 : normK (prodK 120 L5 opts17) = L6 := by
  decide +kernel

theorem p6 : strictPos L6 = true := by
  decide +kernel

theorem s7 : normK (prodK 120 L6 opts31) = L7 := by
  decide +kernel

theorem p7 : strictPos L7 = true := by
  decide +kernel

end K45.S
