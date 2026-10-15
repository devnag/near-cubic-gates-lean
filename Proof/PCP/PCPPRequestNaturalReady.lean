import Proof.PCP.PCPPRequestNaturalFields

/-! Paid local rewinds retain the native source cursor and actual bit-count driver. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNaturalReady
open LocalBitMultitape RepairRepresentation SignedSortKey DecompositionNativeMagnitude
open DecompositionMagnitudeReady
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := MaskedReset.machine PCPPRequestNaturalFields.machine selected
noncomputable def entry (source : List Bool) (pos : ℕ) :=
  Rewind.recording (Composition.leftConfig 6 (Composition.leftConfig 8
    (DecompositionNativeMagnitude.input source pos))) 0
def prepared (source : List Bool) (pos n : ℕ) : Configuration 10 18 :=
  SelectiveReset.finished
    (fun i => if selected i then 0 else
      (DecompositionNativeMagnitude.output source pos (binary (natBitLength n) n) false).heads i)
    (DecompositionNativeMagnitude.output source pos (binary (natBitLength n) n) false).tapes
    (10*natBitLength n+11)

theorem ready_run (pre tail : List Bool) (n : ℕ) :
    ∃ r,runFrom machine (20*natBitLength n+24)
      (entry (pre++natWord n++tail) pre.length)=some r ∧
      r.final=prepared (pre++natWord n++tail) (pre.length+(natWord n).length) n ∧
      r.steps=20*natBitLength n+24 := by
  obtain ⟨p,hp,pf,ps⟩ := PCPPRequestNaturalFields.natural_run pre tail n
  have hh : ∀ i,selected i=true → p.final.heads i ≤ p.steps := by
    intro i hi
    have hne : i≠0 := ((of_decide_eq_true hi : i≠0 ∧ i≠3)).1
    have h := SelectiveReset.prefix_head (prefix_of_run PCPPRequestNaturalFields.machine _ _ p hp).1 i
    have hzero : (Composition.leftConfig 6 (Composition.leftConfig 8
        (DecompositionNativeMagnitude.input (pre++natWord n++tail) pre.length))).heads i=0 := by
      fin_cases i <;> first | contradiction | rfl
    simpa only [hzero,Nat.zero_add] using h
  obtain ⟨r,hr,rf,rs,_⟩ := MaskedReset.reset_run PCPPRequestNaturalFields.machine
    selected _ _ p hp hh
  have ht : 2*p.steps+2=20*natBitLength n+24 := by rw [ps]; omega
  rw [ht] at hr rs
  refine ⟨r,hr,?_,rs⟩
  rw [rf,pf,ps]
  rfl

theorem prepared_flag (pre tail : List Bool) (n : ℕ) :
    (prepared (pre++natWord n++tail) (pre.length+(natWord n).length) n).scanned 8=decide (0<n) :=
  native_present n

end NearCubicWires.RepairOrdinary.PCPPRequestNaturalReady
