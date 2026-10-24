import Romanoff.CertKFinal

/-! Prints the axioms of the kernel-only 45a theorems: `lake env lean Axioms45K.lean`.
`romanoff_U2_K` and `romanoff_v3_K` (same statements as `romanoff_U2` / `romanoff_v3`) depend on `propext`,
`Classical.choice` and `Quot.sound` only: every computation is checked by the kernel (`decide +kernel` shards). -/

#check @Romanoff.romanoff_U2_K
#check @Romanoff.romanoff_v3_K
#print Romanoff.U2Statement
#print Romanoff.V3Statement
#print axioms Romanoff.romanoff_U2_K
#print axioms Romanoff.romanoff_v3_K
#print axioms Romanoff.cert_U2_K
#print axioms Romanoff.cert_v3_K
#print axioms Romanoff.M3.tboundLitK
#print axioms K45.orbits_eq
