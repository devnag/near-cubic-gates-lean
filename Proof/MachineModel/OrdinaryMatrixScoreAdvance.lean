import Proof.MachineModel.OrdinaryMatrixScorePhiLayout
import Proof.Hierarchy.CompetitorReusableDecision

namespace NearCubicWires.RepairOrdinary.MatrixScoreAdvance
open LocalBitMultitape RecoveryRootRound SignedSortKey MatrixScorePhiLayout
open MatrixScoreWeight (zeros)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def idSlots : Fin 2 → Fin 28 := ![22,25]
theorem id_injective : Function.Injective idSlots := by decide
def idPicked : Fin 28 → Option (Fin 2) :=
  ![none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,
    none,none,some 0,none,none,some 1,none,none]
theorem pick_id (i : Fin 28) : RecoveryFocus.pick idSlots i=idPicked i := by
  fin_cases i
  all_goals first
    | decide
    | exact RecoveryFocus.pick_slot idSlots id_injective 0
    | exact RecoveryFocus.pick_slot idSlots id_injective 1

def phiSlots : Fin 4 → Fin 28 := ![22,27,1,25]
theorem phi_injective : Function.Injective phiSlots := by decide
def phiPicked : Fin 28 → Option (Fin 4) :=
  ![none,some 2,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,
    none,none,some 0,none,none,some 3,none,some 1]
theorem pick_phi (i : Fin 28) : RecoveryFocus.pick phiSlots i=phiPicked i := by
  fin_cases i
  all_goals first
    | decide
    | exact RecoveryFocus.pick_slot phiSlots phi_injective 0
    | exact RecoveryFocus.pick_slot phiSlots phi_injective 1
    | exact RecoveryFocus.pick_slot phiSlots phi_injective 2
    | exact RecoveryFocus.pick_slot phiSlots phi_injective 3

noncomputable def bump := RecoveryFocus.machine idSlots FramedIncrement.machine
noncomputable def transform := RecoveryFocus.machine phiSlots MatrixScorePhi.machine
noncomputable def machine := Composition.machine bump transform

theorem ready (w n c : ℕ) (hn : n+1<2^w) (hc : 2*w≤c) :
    ClockJoin.ReadyRun FramedIncrement.machine (4*w+2)
      ![frame (binary w n),zeros c] ![frame (binary w (n+1)),zeros c] := by
  obtain ⟨base,hb,h0,h1,hh,hs,_⟩ := FramedIncrement.increment_run w n c hn hc
  have hi : (Fin.addCases (m := 1) (n := 1) (motive := fun _ => List Bool)
      (fun _ => frame (binary w n)) (fun _ => List.replicate c false))=![frame (binary w n),zeros c] := by
    funext i; fin_cases i <;> rfl
  rw [hi] at hb
  refine ⟨base,hb,?_,hh,hs⟩
  funext i
  fin_cases i
  · exact h0
  · exact h1

theorem advance_run (source : List Bool) (d a c cap w x m id template returnCap : ℕ) (cols : List ℕ)
    (work : Fin 12 → List Bool) (driver counter out : List Bool)
    (ha : a<2^d) (hi : id+1<2^m) (hlen : cols.length ≤ m) (hcols : ∀ z ∈ cols,z<2^d)
    (hm : 2*m ≤ c) (hc : d+cols.length+2 ≤ c) :
    ∃ actual,runFrom machine (advanceBudget d cols.length m c)
      (RecoveryCalls.restarted machine (heads out.length)
        (tapes source (frame (binary d a)) d c cap w x m id template work driver counter out
          returnCap cols))=some actual ∧
      actual.final.heads=heads out.length ∧
      actual.final.tapes=tapes source (frame (binary d (MatrixScorePhi.value cols (id+1)))) d c cap
        w x m (id+1) template work driver counter out returnCap cols ∧
      actual.steps ≤ advanceBudget d cols.length m c := by
  let ambient := tapes source (frame (binary d a)) d c cap w x m id template work driver counter out returnCap cols
  let afterId := tapes source (frame (binary d a)) d c cap w x m (id+1) template work driver counter out returnCap cols
  obtain ⟨first,hf,fh,ft,fs⟩ := CompetitorReusableDecision.bounded_focused_run idSlots id_injective
    FramedIncrement.machine _ _ (ready m id c hi hm) (heads out.length) ambient
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  have firstTapes : first.final.tapes=afterId := by
    rw [ft]
    funext i
    fin_cases i <;> simp [install,pick_id,idPicked,ambient,afterId,tapes,MatrixScoreLeftCycle.tapes,
      MatrixScoreRecordDock.tapes,MatrixScoreLeftFields.tapes,MatrixScoreFoldEntry.tapes,Fin.addCases]
  have hphi := MatrixScorePhi.ready m d (id+1) a c cols hlen hcols ha hc
  obtain ⟨last,hl,lh,lt,ls⟩ := CompetitorReusableDecision.bounded_focused_run phiSlots phi_injective
    MatrixScorePhi.machine _ _ hphi (heads out.length) afterId
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  have hiRun : Composition.restart first.final transform.start=
      RecoveryCalls.restarted transform (heads out.length) afterId := by
    apply configuration_ext
    · rfl
    · exact fh
    · exact firstTapes
  change runFrom transform (MatrixScorePhi.budget cols.length d m c)
    (RecoveryCalls.restarted transform (heads out.length) afterId)=some last at hl
  rw [← hiRun] at hl
  have joined := Composition.run_join bump transform (4*m+2) (MatrixScorePhi.budget cols.length d m c) _
    first last hf hl
  refine ⟨Composition.joinedReceipt first last,joined,lh,?_,?_⟩
  · change last.final.tapes=_
    rw [lt]
    funext i
    fin_cases i <;> simp [install,pick_phi,phiPicked,afterId,tapes,MatrixScoreLeftCycle.tapes,
      MatrixScoreRecordDock.tapes,MatrixScoreLeftFields.tapes,MatrixScoreFoldEntry.tapes,Fin.addCases,
      MatrixScorePhi.zeros,zeros]
  · change first.steps+1+last.steps ≤ _
    unfold advanceBudget
    omega

/-- The new advance inhabits Piece 0's step contract. -/
noncomputable def advanceSpec : AdvanceSpec := ⟨_,machine,advance_run⟩

end NearCubicWires.RepairOrdinary.MatrixScoreAdvance
