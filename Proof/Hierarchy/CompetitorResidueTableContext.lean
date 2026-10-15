import Proof.Hierarchy.CompetitorResidueTableDock
import Proof.Hierarchy.CompetitorMatrixPlaneTable

/-! Literal docking to the existing native TableContext. The source bank
contains cross-bucket P/N contributions; residue execution itself makes no
claim that missing same-bucket contributions have already been included. -/
namespace NearCubicWires.RepairOrdinary.CompetitorResidueTableDock
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
open CompetitorPlaneStream (Cell oldWords countWords countWord)
open CompetitorResidueTable
open CompetitorPlaneTable
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem context_run (b w q pos planeCount : ℕ) (xs : List Cell) (ambient : Fin 34 → List Bool)
    (hcontext : CompetitorPlanePacketPass.Context b w xs ambient)
    (hq : q≤w) (hv : ∀ a∈xs,Valid w a) :
    ∃ r,runFrom machine (budget w q xs.length)
      (RecoveryCalls.restarted machine (heads pos)
        (input (CompetitorPlaneTableEntry.tapes ambient planeCount) q))=some r ∧
      r.steps≤budget w q xs.length ∧ r.final.heads=heads pos ∧
      r.final.tapes 45=residueWords w q xs ∧
      r.final.tapes 35=List.replicate q true ∧ r.final.tapes 36=List.replicate w true ∧
      (∀ i : Fin 35,r.final.tapes (i.castAdd 51)=CompetitorPlaneTableEntry.tapes ambient planeCount i) := by
  exact dock_run (CompetitorPlanePacketPass.capacity w xs.length) w q pos xs
    (List.replicate (CompetitorPlanePacketPass.capacity w xs.length-(oldWords w xs).length) false)
    (CompetitorPlaneTableEntry.tapes ambient planeCount) hcontext.width hcontext.count hcontext.old hq hv

theorem state_valid {n : ℕ} (b p : ℕ) (counts : Fin n → ℕ) (state : State n)
    (hbound : Bounded b p (2*p) state) :
    ∀ a∈cells counts state,Valid (CompetitorPlaneWidth.width b p) a := by
  intro a ha
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  have hsum := (hbound i).trans_lt (CompetitorPlaneWidth.total_fit b p (2*p) (by omega))
  constructor
  · change state.positive i<2^CompetitorPlaneWidth.width b p
    omega
  · change state.negative i<2^CompetitorPlaneWidth.width b p
    omega

theorem state_run {n : ℕ} (b p q pos : ℕ) (state : State n) (ambient : Fin 34 → List Bool)
    (hcontext : TableContext b (CompetitorPlaneWidth.width b p) state ambient)
    (hbound : Bounded b p (2*p) state) (hq : q≤CompetitorPlaneWidth.width b p) :
    ∃ r,runFrom machine (budget (CompetitorPlaneWidth.width b p) q n)
      (RecoveryCalls.restarted machine (heads pos)
        (input (CompetitorPlaneTableEntry.tapes ambient p) q))=some r ∧
      r.steps≤budget (CompetitorPlaneWidth.width b p) q n ∧ r.final.heads=heads pos ∧
      r.final.tapes 45=residueWords (CompetitorPlaneWidth.width b p) q (CompetitorPlaneTable.canonical state) ∧
      r.final.tapes 35=List.replicate q true ∧
      r.final.tapes 36=List.replicate (CompetitorPlaneWidth.width b p) true ∧
      (∀ i : Fin 35,r.final.tapes (i.castAdd 51)=CompetitorPlaneTableEntry.tapes ambient p i) := by
  simpa only [CompetitorPlaneTable.canonical,cells_length] using context_run b (CompetitorPlaneWidth.width b p) q pos p
    (CompetitorPlaneTable.canonical state) ambient hcontext hq (state_valid b p (fun _ => 0) state hbound)

theorem residueWords_eq_counts (w q : ℕ) (xs : List Cell)
    (hv : ∀ a∈xs,Valid w a) (hq : q≤w)
    (hcount : ∀ a∈xs,a.count<2^q)
    (hcongruent : ∀ a∈xs,Int.ModEq ((2:ℤ)^q) ((a.positive:ℤ)-a.negative) a.count) :
    residueWords w q xs=countWords q xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ha : residueWord w q a=countWord q a := by
      unfold residueWord countWord
      rw [CompetitorSignedResidue.residue_eq_count w q a.positive a.negative a.count
        (hv a (by simp)).2 hq (hcount a (by simp)) (hcongruent a (by simp))]
    have ht := ih (fun c hc => hv c (by simp [hc]))
      (fun c hc => hcount c (by simp [hc])) (fun c hc => hcongruent c (by simp [hc]))
    simpa only [residueWords,countWords,List.flatMap_cons,ha] using congrArg (fun xs => countWord q a++xs) ht

theorem count_context_run (b w q pos planeCount : ℕ) (xs : List Cell) (ambient : Fin 34 → List Bool)
    (hcontext : CompetitorPlanePacketPass.Context b w xs ambient)
    (hq : q≤w) (hv : ∀ a∈xs,Valid w a)
    (hcount : ∀ a∈xs,a.count<2^q)
    (hcongruent : ∀ a∈xs,Int.ModEq ((2:ℤ)^q) ((a.positive:ℤ)-a.negative) a.count) :
    ∃ r,runFrom machine (budget w q xs.length)
      (RecoveryCalls.restarted machine (heads pos)
        (input (CompetitorPlaneTableEntry.tapes ambient planeCount) q))=some r ∧
      r.steps≤budget w q xs.length ∧ r.final.heads=heads pos ∧
      r.final.tapes 45=countWords q xs ∧
      r.final.tapes 35=List.replicate q true ∧ r.final.tapes 36=List.replicate w true ∧
      (∀ i : Fin 35,r.final.tapes (i.castAdd 51)=CompetitorPlaneTableEntry.tapes ambient planeCount i) := by
  simpa only [residueWords_eq_counts w q xs hv hq hcount hcongruent] using
    context_run b w q pos planeCount xs ambient hcontext hq hv

end NearCubicWires.RepairOrdinary.CompetitorResidueTableDock
