import Proof.Circuits.DecompositionAtomLayout

/-! Complete cold signed atom, including literal zero. Every native field is
parsed exactly once and its original source cursor is retained. -/
namespace NearCubicWires.RepairOrdinary.DecompositionAtom
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem atom_run (pre tail : List Bool) (z : ℤ) :
    ∃ r,runFrom machine (budget z) (entry (pre++intWord z++tail) pre.length)=some r ∧
      (∃ padding,r.final.tapes 162=frame (CanonicalBinary.encodeInt z).bits++
        List.replicate padding false) ∧
      r.final.heads 162=0 ∧ r.final.tapes 0=pre++intWord z++tail ∧
      r.final.heads 0=pre.length+(intWord z).length ∧ r.steps ≤ budget z := by
  obtain ⟨base,hb,bf,_⟩ := prepare_run pre tail z
  have core : ∃ n≤budget z,∃ heads tapes,
      Timed machine n (entry (pre++intWord z++tail) pre.length)
        (RecoveryCalls.stopped sizes heads tapes) ∧
      (∃ padding,tapes 162=frame (CanonicalBinary.encodeInt z).bits++List.replicate padding false) ∧
      heads 162=0 ∧ tapes 0=pre++intWord z++tail ∧
      heads 0=pre.length+(intWord z).length := by
    by_cases hz : 0<z.natAbs
    · have hn : next 0 base.final.control base.final.scanned=some 1 := by
        rw [bf]
        simp [next,prepared_flag,hz]
      obtain ⟨n,hn,hprefix⟩ := call_receipt sizes programs 0 next 0 1 _ _ base hb hn
      rw [bf,positive_entry] at hprefix
      obtain ⟨last,hl,lt,lh,l0,lh0,_⟩ := DecompositionSignedTail.tail_run pre tail z hz
      obtain ⟨m,hm,hstop⟩ := stop_receipt sizes programs 0 next 1 _ _ last hl (by rfl)
      refine ⟨n+m,?_,last.final.heads,last.final.tapes,hprefix.trans hstop,?_,lh,l0,lh0⟩
      · unfold budget
        omega
      · exact ⟨_,lt⟩
    · have hz0 : z=0 := Int.natAbs_eq_zero.mp (by omega)
      have hn : next 0 base.final.control base.final.scanned=some 2 := by
        rw [bf]
        simp [next,prepared_flag,hz]
      obtain ⟨n,hn,hprefix⟩ := call_receipt sizes programs 0 next 0 2 _ _ base hb hn
      rw [bf] at hprefix
      obtain ⟨last,hl,lf,ls⟩ := zero_run (prepared pre tail z).heads (prepared pre tail z).tapes
        (by rfl) (by rfl)
      obtain ⟨m,hm,hstop⟩ := stop_receipt sizes programs 0 next 2 _ _ last hl (by rfl)
      refine ⟨n+m,?_,last.final.heads,last.final.tapes,hprefix.trans hstop,?_,?_,?_,?_⟩
      · unfold budget
        omega
      · refine ⟨0,?_⟩
        rw [lf,hz0]
        simp [zeroOutput,show CanonicalBinary.encodeInt (0 : ℤ)=0 from
          (CanonicalBinary.encodeInt_eq_zero_iff 0).mpr rfl,frame]
      · rw [lf]; rfl
      · rw [lf]; rfl
      · rw [lf]; rfl
  obtain ⟨n,hn,heads,tapes,path,ht,hh,h0,hh0⟩ := core
  obtain ⟨r,hr,rf,rs⟩ := path.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have more := runFrom_moreFuel machine n (budget z-n) _ r hr
  rw [Nat.add_sub_of_le hn] at more
  refine ⟨r,more,?_,?_,?_,?_,?_⟩
  · rw [rf]; exact ht
  · rw [rf]; exact hh
  · rw [rf]; exact h0
  · rw [rf]; exact hh0
  · omega

end NearCubicWires.RepairOrdinary.DecompositionAtom
