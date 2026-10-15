import Proof.MachineModel.OrdinaryMatrixScoreLeftCycle
import Proof.MachineModel.OrdinaryMatrixScorePhi

namespace NearCubicWires.RepairOrdinary.MatrixScorePhiLayout
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

/-- Heads of the 28-tape carrier: the cycle's heads, and the `φ` tape at cell 0. -/
def heads (opos : ℕ) : Fin 28 → ℕ :=
  Fin.addCases (m := 27) (n := 1) (motive := fun _ => ℕ) (MatrixScoreLeftCycle.heads opos) (fun _ => 0)

/-- Tapes of the 28-tape carrier: the cycle's tapes, and the `φ` columns as tape 27. -/
def tapes (source assignment : List Bool) (d c cap w x m id template : ℕ)
    (work : Fin 12 → List Bool) (driver counter out : List Bool) (returnCap : ℕ) (cols : List ℕ) :
    Fin 28 → List Bool :=
  Fin.addCases (m := 27) (n := 1) (motive := fun _ => List Bool)
    (MatrixScoreLeftCycle.tapes source assignment d c cap w x m id template work driver counter out returnCap)
    (fun _ => MatrixScorePhi.columnsWord d cols)

/-- The fixed budget of the new advance: the id increment of today's `MatrixScoreAdvance`
(`4m+2`), one composition step, and one `φ` evaluation. -/
def advanceBudget (d k m c : ℕ) : ℕ := (4*m+2)+1+MatrixScorePhi.budget k d m c

/-- PIECE A contract. The id tape is 22, the assignment tape 1, the zero scratch 25 and the
`φ` tape 27 (slots of `MatrixScorePhi.ready`: 22, 27, 1, 25). -/
structure AdvanceSpec where
  states : ℕ
  machine : Machine 28 states
  run : ∀ (source : List Bool) (d a c cap w x m id template returnCap : ℕ) (cols : List ℕ)
      (work : Fin 12 → List Bool) (driver counter out : List Bool),
      a<2^d → id+1<2^m → cols.length ≤ m → (∀ z ∈ cols,z<2^d) → 2*m ≤ c → d+cols.length+2 ≤ c →
      ∃ actual,runFrom machine (advanceBudget d cols.length m c)
        (RecoveryCalls.restarted machine (heads out.length)
          (tapes source (frame (binary d a)) d c cap w x m id template work driver counter out
            returnCap cols))=some actual ∧
        actual.final.heads=heads out.length ∧
        actual.final.tapes=tapes source (frame (binary d (MatrixScorePhi.value cols (id+1)))) d c cap
          w x m (id+1) template work driver counter out returnCap cols ∧
        actual.steps ≤ advanceBudget d cols.length m c

end NearCubicWires.RepairOrdinary.MatrixScorePhiLayout
