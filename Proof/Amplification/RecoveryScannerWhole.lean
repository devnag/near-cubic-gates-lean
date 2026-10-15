import Proof.Amplification.RecoveryScannerRead

/-! The complete scanner copy executes cold preparation and the accepted
raw-view reader without changing the172 tapes retained for final checking. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdScanner
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def scanProgram := Composition.machine program readProgram
def scanBudget (bits word : List Bool) := RecoveryColdView.coldBudget bits word+1+536870912*(width bits+1)^4

theorem scan_run (bits word : List Bool) (h : Fin 172→Nat) (a : Fin 172→List Bool)
    (hh : h 0=0 ∧ h 1=0) (ht : a 0=frame bits ∧ a 1=frame word)
    (table : List (Nat×Bool)) (tail : List Bool)
    (hp : readList (limit bits) (readEntry (width bits)) word=some (table,tail)) :
    ∃ bit r,runFrom scanProgram (scanBudget bits word)
        ⟨scanProgram.start,heads h,tapes a⟩=some r ∧
      r.steps ≤ scanBudget bits word ∧ r.final.heads flag=0 ∧ r.final.tapes flag=[bit] ∧
      (fun i : Fin 172=>r.final.heads (i.castAdd 98))=h ∧
      (fun i : Fin 172=>r.final.tapes (i.castAdd 98))=a ∧
      (bit=true → ∃ pos,r.final.heads source=2*pos ∧ r.final.tapes source=frame word) := by
  obtain ⟨first,hfirst,_,hfh,hft,hready⟩ := prepare_run bits word h a hh ht table tail hp
  obtain ⟨count,last,_,hlast,_,hlh,hlt,hkeepH,hkeepT,hgood⟩ := read_run bits word first.final.heads first.final.tapes hready
  have hb : RecoveryRawViewEntry.budget (view bits word (2*(count*(width bits+2)+1)))≤
      536870912*(width bits+1)^4 := by
    have hbound := RecoveryRawViewEntry.budget_bound _ (view_valid bits word (2*(count*(width bits+2)+1)))
    rw [view_width] at hbound
    exact hbound
  have hm := runFrom_moreFuel readProgram
    (RecoveryRawViewEntry.budget (view bits word (2*(count*(width bits+2)+1))))
    (536870912*(width bits+1)^4-RecoveryRawViewEntry.budget (view bits word (2*(count*(width bits+2)+1))))
    _ last hlast
  rw [Nat.add_sub_of_le hb] at hm
  have hi : Composition.restart first.final readProgram.start=
      (⟨readProgram.start,first.final.heads,first.final.tapes⟩ : Configuration 270 _) := rfl
  rw [←hi] at hm
  have hr := Composition.run_join program readProgram (RecoveryColdView.coldBudget bits word)
    (536870912*(width bits+1)^4) _ first last hfirst hm
  let r := Composition.joinedReceipt first last
  refine ⟨_,r,hr,runFrom_steps_le scanProgram (scanBudget bits word) _ r hr,hlh,hlt,
    hkeepH.trans hfh,hkeepT.trans hft,?_⟩
  intro hbit
  apply hgood
  rw [hlt,hbit]

end NearCubicWires.RepairOrdinary.RecoveryColdScanner
