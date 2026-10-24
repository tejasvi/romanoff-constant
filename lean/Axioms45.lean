import Romanoff.Theorems

/-! Prints the 45a statements and the axioms of the main theorems: `lake env lean Axioms45.lean`.
`romanoff_U2` and `romanoff_v3` depend on `propext`, `Classical.choice`, `Quot.sound` and four `native_decide` checks
(the M3 certificate checks `certOK_data`, `sumsOK_data`, `teffD_eq`, and the certificate value `cert_U2_lit` resp.
`cert_v3_lit`); the analytic reduction `lagR_le_liminf` depends on the three standard axioms only. -/

#print Romanoff.IsRomanoff
#print Romanoff.count
#print Romanoff.dens
#print Romanoff.U2Statement
#print Romanoff.V3Statement
#print Romanoff.ESP28
#print Romanoff.JTProp2
#print Romanoff.PNTAP
#print Romanoff.R0Bound
#print Romanoff.ellPrimes
#check @Romanoff.lowerDensityGe_iff
#check @Romanoff.romanoff_U2
#check @Romanoff.romanoff_v3
#check @Romanoff.lagR_le_liminf
#print axioms Romanoff.romanoff_U2
#print axioms Romanoff.romanoff_v3
#print axioms Romanoff.lagR_le_liminf
#print axioms Romanoff.M3.tboundLit
