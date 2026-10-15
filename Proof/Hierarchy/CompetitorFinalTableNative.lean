import Proof.Hierarchy.CompetitorFinalTableController

/-! Literal final supplier on native35 plus actual same/Q/U/parity fields.
The finite-grid diagnostic precedes this proved quantitative envelope. -/
namespace NearCubicWires.RepairOrdinary.CompetitorFinalTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorPlaneTable CompetitorOddRowSlice
open CompetitorPlaneStream (oldWords)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_bound (u w q : ℕ) (hq : q≤w) : budget u w q≤622000*(u*u+1)*(w+1)^2 := by
  have hm := CompetitorBankMergeDock.budget_bound w (u*u)
  have hr := CompetitorResidueTableDock.budget_bound w q (u*u) hq
  have hs := CompetitorOddRowSliceDock.budget_bound u q
  have hq' : q+1≤(w+1)^2 := by nlinarith
  have hmul := Nat.mul_le_mul_left (256*(u*u+1)) hq'
  have hp : 0<(u*u+1)*(w+1)^2 := by positivity
  unfold budget oddBudget
  nlinarith

theorem native_run {u : ℕ} (b w q pos : ℕ) (odd : Bool)
    (cross same : State (u*u)) (f : Fin u → Fin u → ℕ) (ambient : Fin 35 → List Bool)
    (hc : TableContext b w cross (fun i : Fin 34 => ambient (i.castAdd 1)))
    (hq : q≤w) (he : odd=true → u/2+u/2=u)
    (hfit : ∀ i,cross.positive i+same.positive i<2^w ∧ cross.negative i+same.negative i<2^w)
    (hcount : ∀ i : Fin (u*u),f i.divNat i.modNat<2^q)
    (hcongruent : ∀ i : Fin (u*u),Int.ModEq ((2:ℤ)^q)
      (((cross.positive i+same.positive i:ℕ):ℤ)-((cross.negative i+same.negative i:ℕ):ℤ)) (f i.divNat i.modNat)) :
    ∃ r,runFrom machine (budget u w q)
      (RecoveryCalls.restarted machine (heads pos) (input ambient (oldWords w (canonical same)) q u odd))=some r ∧
      r.steps≤622000*(u*u+1)*(w+1)^2 ∧ r.final.heads=heads pos ∧
      r.final.tapes 141=word q odd f ∧
      Native b w (CompetitorBankMergeDock.stateAdd cross same) r.final.tapes ∧
      r.final.tapes 35=oldWords w (canonical same) ∧
      r.final.tapes 36=List.replicate q true ∧ r.final.tapes 37=UnaryTemplate.tape u ∧ r.final.tapes 38=[odd] ∧
      (∀ i : Fin 35,i≠19 → r.final.tapes (i.castAdd 124)=ambient i) := by
  have hn : Native b w cross (input ambient (oldWords w (canonical same)) q u odd) := by
    unfold Native
    change TableContext b w cross (fun i : Fin 34 => input ambient (oldWords w (canonical same)) q u odd ((i.castAdd 1).castAdd 124))
    simpa only [input,Fin.addCases_left] using hc
  have hf : ∀ i : Fin 159,39 ≤ i.val → input ambient (oldWords w (canonical same)) q u odd i=[] := by
    intro i hi
    fin_cases i <;> first | (solve | norm_num at hi) | rfl
  obtain ⟨r,hr,hs,hh,ht,hctx,hkeep⟩ := table_run b w q pos odd cross same f
    (input ambient (oldWords w (canonical same)) q u odd) hn rfl rfl rfl rfl hf hq he hfit hcount hcongruent
  refine ⟨r,hr,hs.trans (budget_bound u w q hq),hh,ht,hctx,hkeep 35 (by decide),
    hkeep 36 (by decide),hkeep 37 (by decide),hkeep 38 (by decide),?_⟩
  intro i hi
  have hi' : (i.castAdd 4 : Fin 39)≠19 := fun h => hi (Fin.ext (congrArg (fun j : Fin 39 => j.val) h))
  have ht' := hkeep (i.castAdd 4) hi'
  change r.final.tapes (i.castAdd 124)=input ambient (oldWords w (canonical same)) q u odd (i.castAdd 124) at ht'
  simpa only [input,Fin.addCases_left] using ht'

end NearCubicWires.RepairOrdinary.CompetitorFinalTable
