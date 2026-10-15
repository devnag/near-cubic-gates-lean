import Proof.Amplification.RecoveryMarkerAtomGraph

/-! Whole marker-field save and optional actual empty-clause test,
including the physical Boolean return and both fixed mode branches. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarkerAtom
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryMarkerClause
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem save_trace (which : Fin 3) (x : State) (bits : List Bool)
    (hx : x.Valid) (hw : bits.length=x.width) (hf : x.inner.data.fields 0=frame bits) :
    ∃ n,n ≤ saveBudget x.width ∧ Timed (machine which) n
      (controlConfig (RecoveryCalls.code (sizes which) 2)
        (initialConfiguration (programs which 2) x.tapes))
      (RecoveryCalls.stopped (sizes which) (fun _=>0) (final which x).tapes) := by
  have hsave := RecoveryMarkerSave.save_ready x which bits hx hw hf
  have hv := RecoveryMarkerSave.saved_valid x which hx
  by_cases hwhich : which.val=1
  · have h0 := hsave.call (sizes which) (programs which) 0 (next which) 2 4 (by
      intro q
      change some (if which.val=1 then (4 : Fin 6) else 3)=some 4
      rw [if_pos hwhich])
    have h1 := (RecoveryMarkerFlags.answer_ready (saved which x) true).stop
      (sizes which) (programs which) 0 (next which) 4 (by intro q; rfl)
    refine ⟨(8*x.width+8+1)+2,?_,?_⟩
    · unfold saveBudget
      omega
    · have hfina : final which x=RecoveryMarkerFlags.answered (saved which x) true := by
        simp only [final,tailAnswer,tested,hwhich,ite_true]
      rw [hfina]
      exact h0.trans h1
  · have h0 := hsave.call (sizes which) (programs which) 0 (next which) 2 3 (by
      intro q
      change some (if which.val=1 then (4 : Fin 6) else 3)=some 3
      rw [if_neg hwhich])
    have he := empty_ready (saved which x) hv.1
    have hc := RecoveryStoredListCell.time_bound (saved which x).inner.data.bits
    unfold RecoveryStoredListCell.budget at hc
    change RecoveryStoredListCell.time (saved which x).inner.data.bits ≤ 262144*((saved which x).width+1)^2 at hc
    have hw' : (saved which x).width=x.width := RecoveryMarkerSave.saved_width x which
    rw [hw'] at hc
    cases ha : (emptyStep (saved which x)).inner.data.flag
    · have h1 := he.call (sizes which) (programs which) 0 (next which) 3 4 (by
        intro q
        change some (if readTapeBit [(emptyStep (saved which x)).inner.data.flag] 0 then (5 : Fin 6) else 4)=some 4
        change some (if (emptyStep (saved which x)).inner.data.flag then (5 : Fin 6) else 4)=some 4
        rw [ha]; rfl)
      have h2 := (RecoveryMarkerFlags.answer_ready (emptyStep (saved which x)) true).stop
        (sizes which) (programs which) 0 (next which) 4 (by intro q; rfl)
      refine ⟨(8*x.width+8+1)+((RecoveryStoredListCell.time (saved which x).inner.data.bits+1)+2),?_,?_⟩
      · unfold saveBudget
        omega
      · have hfina : final which x=RecoveryMarkerFlags.answered (emptyStep (saved which x)) true := by
          simp only [final,tailAnswer,tested,hwhich,ite_false,ha,Bool.not_false]
        rw [hfina]
        exact h0.trans (h1.trans h2)
    · have h1 := he.call (sizes which) (programs which) 0 (next which) 3 5 (by
        intro q
        change some (if readTapeBit [(emptyStep (saved which x)).inner.data.flag] 0 then (5 : Fin 6) else 4)=some 5
        change some (if (emptyStep (saved which x)).inner.data.flag then (5 : Fin 6) else 4)=some 5
        rw [ha]; rfl)
      have h2 := (RecoveryMarkerFlags.answer_ready (emptyStep (saved which x)) false).stop
        (sizes which) (programs which) 0 (next which) 5 (by intro q; rfl)
      refine ⟨(8*x.width+8+1)+((RecoveryStoredListCell.time (saved which x).inner.data.bits+1)+2),?_,?_⟩
      · unfold saveBudget
        omega
      · have hfina : final which x=RecoveryMarkerFlags.answered (emptyStep (saved which x)) false := by
          simp only [final,tailAnswer,tested,hwhich,ite_false,ha,Bool.not_true]
        rw [hfina]
        exact h0.trans (h1.trans h2)

theorem sign_trace (which : Fin 3) (x : State) (bits : List Bool)
    (hx : x.Valid) (hw : bits.length=x.width) (hf : x.inner.data.fields 0=frame bits) :
    ∃ n,n ≤ saveBudget x.width+2 ∧ Timed (machine which) n
      (controlConfig (RecoveryCalls.code (sizes which) (if which.val=0 then 1 else 2))
        (initialConfiguration (programs which (if which.val=0 then 1 else 2)) x.tapes))
      (RecoveryCalls.stopped (sizes which) (fun _=>0) (final which (withSign which x)).tapes) := by
  by_cases hwhich : which.val=0
  · have h0 := (RecoveryMarkerFlags.flat_ready x).call (sizes which) (programs which) 0 (next which) 1 2 (by intro q; rfl)
    have hv : (RecoveryMarkerFlags.flat x).Valid := hx
    obtain ⟨n,hn,h⟩ := save_trace which (RecoveryMarkerFlags.flat x) bits hv hw hf
    refine ⟨2+n,by change n ≤ saveBudget x.width at hn; omega,?_⟩
    rw [show (if which.val=0 then (1 : Fin 6) else 2)=1 from if_pos hwhich]
    rw [show withSign which x=RecoveryMarkerFlags.flat x from if_pos hwhich]
    exact h0.trans h
  · obtain ⟨n,hn,h⟩ := save_trace which x bits hx hw hf
    refine ⟨n,by omega,?_⟩
    rw [show (if which.val=0 then (1 : Fin 6) else 2)=2 from if_neg hwhich]
    rw [show withSign which x=x from if_neg hwhich]
    exact h

end NearCubicWires.RepairOrdinary.RecoveryMarkerAtom
