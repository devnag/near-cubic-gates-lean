import Proof.Amplification.RecoveryTablesAmbientLayout

/-! Both reused scalar drivers return exactly, so table materialization
preserves all172 tapes reserved for the final raw/default branch. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdTablesAmbient
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem low_geometry : ∀ j : Fin 12,(slots j).val<172 → j=2 ∨ j=6 := by decide
theorem old_other (i : Fin 172) (h62 : i≠62) (h96 : i≠96) : ∀ j,slots j≠i.castAdd 107 := by
  intro j he
  have hv : (slots j).val=i.val := congrArg (fun k : Fin 279=>k.val) he
  have hj := low_geometry j (by rw [hv]; exact i.isLt)
  rcases hj with hj | hj
  · subst j
    apply h96
    exact Fin.ext hv.symm
  · subst j
    apply h62
    exact Fin.ext hv.symm

theorem old_retained {s : Nat} (h : Fin 270→Nat) (a : Fin 270→List Bool) (c : Configuration 12 s)
    (hh : c.heads 6=h 62 ∧ c.heads 2=h 96)
    (ht : c.tapes 6=a 62 ∧ c.tapes 2=a 96) :
    (fun i : Fin 172=>(RecoveryFocus.config slots (heads h) (tapes a) c).heads (i.castAdd 107))=
      (fun i=>h (i.castAdd 98)) ∧
    (fun i : Fin 172=>(RecoveryFocus.config slots (heads h) (tapes a) c).tapes (i.castAdd 107))=
      (fun i=>a (i.castAdd 98)) := by
  constructor
  · funext i
    by_cases h62 : i=62
    · subst i
      change (RecoveryFocus.config slots (heads h) (tapes a) c).heads (slots 6)=_
      rw [show (62 : Fin 172).castAdd 98=(62 : Fin 270) by decide]
      simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective] using hh.1
    · by_cases h96 : i=96
      · subst i
        change (RecoveryFocus.config slots (heads h) (tapes a) c).heads (slots 2)=_
        rw [show (96 : Fin 172).castAdd 98=(96 : Fin 270) by decide]
        simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective] using hh.2
      · have hn : ¬∃ j,slots j=i.castAdd 107 := by rintro ⟨j,hj⟩; exact old_other i h62 h96 j hj
        simp only [RecoveryFocus.config,RecoveryFocus.pick,hn,↓reduceDIte]
        rw [←show (i.castAdd 98).castAdd 9=i.castAdd 107 from Fin.ext rfl]
        simp only [heads,Fin.addCases_left]
  · funext i
    by_cases h62 : i=62
    · subst i
      change (RecoveryFocus.config slots (heads h) (tapes a) c).tapes (slots 6)=_
      rw [show (62 : Fin 172).castAdd 98=(62 : Fin 270) by decide]
      simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective] using ht.1
    · by_cases h96 : i=96
      · subst i
        change (RecoveryFocus.config slots (heads h) (tapes a) c).tapes (slots 2)=_
        rw [show (96 : Fin 172).castAdd 98=(96 : Fin 270) by decide]
        simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective] using ht.2
      · have hn : ¬∃ j,slots j=i.castAdd 107 := by rintro ⟨j,hj⟩; exact old_other i h62 h96 j hj
        simp only [RecoveryFocus.config,RecoveryFocus.pick,hn,↓reduceDIte]
        rw [←show (i.castAdd 98).castAdd 9=i.castAdd 107 from Fin.ext rfl]
        simp only [tapes,Fin.addCases_left]

theorem restored_retained (word innerBits outerBits : List Bool) (k n m width cap logged : Nat)
    (h : Fin 270→Nat) (a : Fin 270→List Bool) (ha : Sources word k width cap h a) :
    (fun i : Fin 172=>(RecoveryFocus.config slots (heads h) (tapes a)
      (RecoveryColdTables.restored word innerBits outerBits n m width cap logged)).heads (i.castAdd 107))=
      (fun i=>h (i.castAdd 98)) ∧
    (fun i : Fin 172=>(RecoveryFocus.config slots (heads h) (tapes a)
      (RecoveryColdTables.restored word innerBits outerBits n m width cap logged)).tapes (i.castAdd 107))=
      (fun i=>a (i.castAdd 98)) := by
  apply old_retained
  · exact ⟨ha.widthHead.symm,ha.capHead.symm⟩
  · exact ⟨ha.widthTape.symm,ha.capTape.symm⟩

end NearCubicWires.RepairOrdinary.RecoveryColdTablesAmbient
