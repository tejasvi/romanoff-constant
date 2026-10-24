import K45.G.Opts

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45.S

open R45 K45 K45.G

theorem opts3_eq : optsP 120 3 = opts3 := by
  decide +kernel

theorem opts3_pos : ∀ x ∈ opts3, 0 < x.2 := by
  decide +kernel

theorem opts5_eq : optsP 120 5 = opts5 := by
  decide +kernel

theorem opts5_pos : ∀ x ∈ opts5, 0 < x.2 := by
  decide +kernel

theorem opts7_eq : optsP 120 7 = opts7 := by
  decide +kernel

theorem opts7_pos : ∀ x ∈ opts7, 0 < x.2 := by
  decide +kernel

theorem opts11_eq : optsP 120 11 = opts11 := by
  decide +kernel

theorem opts11_pos : ∀ x ∈ opts11, 0 < x.2 := by
  decide +kernel

theorem opts13_eq : optsP 120 13 = opts13 := by
  decide +kernel

theorem opts13_pos : ∀ x ∈ opts13, 0 < x.2 := by
  decide +kernel

theorem opts17_eq : optsP 120 17 = opts17 := by
  decide +kernel

theorem opts17_pos : ∀ x ∈ opts17, 0 < x.2 := by
  decide +kernel

theorem opts31_eq : optsP 120 31 = opts31 := by
  decide +kernel

theorem opts31_pos : ∀ x ∈ opts31, 0 < x.2 := by
  decide +kernel

theorem opts41_eq : optsP 120 41 = opts41 := by
  decide +kernel

theorem opts41_pos : ∀ x ∈ opts41, 0 < x.2 := by
  decide +kernel

theorem opts241_eq : optsP 120 241 = opts241 := by
  decide +kernel

theorem opts241_pos : ∀ x ∈ opts241, 0 < x.2 := by
  decide +kernel

end K45.S
