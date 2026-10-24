import GK.Ev

/-! k45g: helpers for the compiled cross-checks and generators (not part of the proof). -/

open R45 R45.EVG

namespace R45.GK

/-- Lean syntax of a tree (for generating literals). -/
def Acc.lean : Acc → String
  | .leaf a q => s!"(.leaf {a} {q})"
  | .node l r => s!"(.node {l.lean} {r.lean})"

def keysG : List (Nat × Nat) := foldOrbits 120 baseP

end R45.GK
