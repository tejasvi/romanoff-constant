import K45G.LG_000
import K45G.LG_001
import K45G.LG_002
import K45G.LG_003
import K45G.LG_004
import K45G.LG_005
import K45G.LG_006
import K45G.LG_007

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace K45G

open R45

/-- The BASE fold list of U3g/V4g in chunks of 123 keys. -/
def LGchunks : List (List (Nat × Nat)) := [lg_000, lg_001, lg_002, lg_003, lg_004, lg_005, lg_006, lg_007, lg_008, lg_009, lg_010, lg_011, lg_012, lg_013, lg_014, lg_015, lg_016, lg_017, lg_018, lg_019, lg_020, lg_021, lg_022, lg_023, lg_024, lg_025, lg_026, lg_027, lg_028, lg_029, lg_030, lg_031, lg_032, lg_033, lg_034, lg_035, lg_036, lg_037, lg_038, lg_039, lg_040, lg_041, lg_042, lg_043, lg_044, lg_045, lg_046, lg_047, lg_048, lg_049, lg_050, lg_051, lg_052, lg_053, lg_054, lg_055, lg_056, lg_057, lg_058, lg_059, lg_060, lg_061, lg_062, lg_063]

/-- The BASE fold list of U3g/V4g: `foldOrbits 120 [3, 5, 7, 11, 13, 17, 31, 241]` (`K45G.foldBase_eq`). -/
def LG : List (Nat × Nat) := LGchunks.flatten

end K45G
