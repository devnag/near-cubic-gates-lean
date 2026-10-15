import Proof.Circuits.DecompositionNativeMagnitude

/-! Paid local rewinds after parsing a native signed field. The original
source cursor and the real bit-count sentinel remain live. The Boolean
stream and sign/nonzero fields are ready for the shared serializer call. -/
namespace NearCubicWires.RepairOrdinary.DecompositionMagnitudeReady
open LocalBitMultitape RepairRepresentation SignedSortKey DecompositionNativeMagnitude
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem present_value (bits : List Bool) :
    DecompositionBitFields.present bits=decide (0<RadixSemantics.value bits) := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    change (b || DecompositionBitFields.present bits)=decide (0<(b.toNat+2*RadixSemantics.value bits))
    rw [ih]
    cases b <;> simp

theorem native_present (n : ℕ) :
    DecompositionBitFields.present (binary (natBitLength n) n)=decide (0<n) := by
  rw [present_value]
  have hf : n<2^natBitLength n := Nat.lt_pow_succ_log_self (by decide) n
  rw [binary_value (natBitLength n) n hf]

def selected (i : Fin 9) := decide (i≠0 ∧ i≠3)
noncomputable def machine := MaskedReset.machine DecompositionNativeMagnitude.machine selected
noncomputable def entry (source : List Bool) (pos : ℕ) :=
  Rewind.recording (Composition.leftConfig 6 (Composition.leftConfig 8
    (DecompositionNativeMagnitude.input source pos))) 0
def prepared (source : List Bool) (pos : ℕ) (z : ℤ) : Configuration 10 18 :=
  SelectiveReset.finished
    (fun i => if selected i then 0 else
      (DecompositionNativeMagnitude.output source pos (binary (natBitLength z.natAbs) z.natAbs)
        (decide (z<0))).heads i)
    (DecompositionNativeMagnitude.output source pos (binary (natBitLength z.natAbs) z.natAbs)
      (decide (z<0))).tapes
    (10*natBitLength z.natAbs+11)

theorem ready_run (pre tail : List Bool) (z : ℤ) :
    ∃ r,runFrom machine (20*natBitLength z.natAbs+24)
      (entry (pre++intWord z++tail) pre.length)=some r ∧
      r.final=prepared (pre++intWord z++tail) (pre.length+(intWord z).length) z ∧
      r.steps=20*natBitLength z.natAbs+24 := by
  obtain ⟨p,hp,pf,ps⟩ := magnitude_run pre tail z
  have hh : ∀ i,selected i=true → p.final.heads i ≤ p.steps := by
    intro i hi
    have hne : i≠0 := ((of_decide_eq_true hi : i≠0 ∧ i≠3)).1
    have h := SelectiveReset.prefix_head (prefix_of_run DecompositionNativeMagnitude.machine _ _ p hp).1 i
    have hzero : (Composition.leftConfig 6 (Composition.leftConfig 8
        (DecompositionNativeMagnitude.input (pre++intWord z++tail) pre.length))).heads i=0 := by
      fin_cases i <;> first | contradiction | rfl
    simpa only [hzero,Nat.zero_add] using h
  obtain ⟨r,hr,rf,rs,_⟩ := MaskedReset.reset_run DecompositionNativeMagnitude.machine
    selected _ _ p hp hh
  have ht : 2*p.steps+2=20*natBitLength z.natAbs+24 := by rw [ps]; omega
  rw [ht] at hr rs
  refine ⟨r,hr,?_,rs⟩
  rw [rf,pf,ps]
  rfl

end NearCubicWires.RepairOrdinary.DecompositionMagnitudeReady
