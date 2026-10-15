import Proof.CaseAnalysis.RowsIntegerLoad

/-! The checked integer program uses the same loaded raw field, appends
its signed native word, and retains the exact codec verdict for the fold. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsIntegerRound
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

@[simp] theorem core_output_slot : coreSlots 213=(213 : Fin 220):=by decide
@[simp] theorem core_flag_slot : coreSlots 211=(211 : Fin 220):=by decide
def scratchCore (i : Fin 214) : Fin 215:=⟨(scratchSlots i).val,scratch_small i⟩
theorem scratch_core (i : Fin 214) : coreSlots (scratchCore i)=scratchSlots i:=Fin.ext rfl

noncomputable def parser:=RecoveryFocus.machine coreSlots CloseoutRowsIntegerReady.machine
theorem parse_run (w position : ℕ) (bits out source : List Bool) (flag : Bool)
    (hw : bits.length ≤ w) : ∃ result,
    runFrom parser (CloseoutRowsIntegerReady.budget bits)
      (cfg parser.start (CloseoutRowsIntegerReady.capacity w) position bits out source flag)=some result ∧
      result.steps ≤ CloseoutRowsIntegerReady.budget bits ∧
      result.final.heads=heads (out++CloseoutRowsCheckedInteger.produced bits) position ∧
      Stored (CloseoutRowsIntegerReady.capacity w) (out++CloseoutRowsCheckedInteger.produced bits) source flag result.final.tapes ∧
      (readTapeBit (result.final.tapes 211) 0=true ↔ (CanonicalBinary.decodeInt (value bits)).isSome):=by
  obtain ⟨r,hrun,rs,rt,rh,rf,rlocal⟩:=CloseoutRowsIntegerReady.integer_run w bits out hw
  obtain ⟨a,ha,_,asteps,ah,atape,keep⟩:=RecoveryFocus.dock coreSlots core_injective
    CloseoutRowsIntegerReady.machine _ (heads out position) (data (CloseoutRowsIntegerReady.capacity w) bits out source flag) _
    (heads_core _ _ _ _) (data_core _ _ _ _ _) r hrun
  have outside (i : Fin 5) : ∀ j : Fin 215,coreSlots j≠i.natAdd 215:=by
    intro j h
    have hv:=congrArg Fin.val h
    change j.val=215+i.val at hv
    omega
  have aextras (i : Fin 5) : a.final.tapes (i.natAdd 215)=extra (CloseoutRowsIntegerReady.capacity w) source flag i:=
    ((keep (i.natAdd 215) (outside i)).2).trans (data_extra _ _ _ _ _ i)
  refine ⟨a,ha,asteps.trans_le rs,?_,?_,?_⟩
  · funext i
    refine Fin.addCases (m:=215) (n:=5) ?_ ?_ i
    · intro j
      change a.final.heads (coreSlots j)=heads (out++CloseoutRowsCheckedInteger.produced bits) position (coreSlots j)
      rw [ah,heads_core w position bits (out++CloseoutRowsCheckedInteger.produced bits),
        CloseoutRowsIntegerReady.entry_heads]
      by_cases hj:j=213
      · subst j
        simpa only [ite_true] using rh
      · simpa only [if_neg hj] using (rlocal j hj).1
    · intro j
      rw [(keep (j.natAdd 215) (outside j)).1]
      have h0:(j.natAdd 215 : Fin 220)≠213:=by
        intro h
        have hv:=congrArg Fin.val h
        change 215+j.val=213 at hv
        omega
      simp only [heads,if_neg h0]
  · refine ⟨?_,?_,aextras⟩
    · intro i
      rw [←scratch_core i,atape]
      exact (rlocal (scratchCore i) (by
        intro h
        have hv:=congrArg Fin.val h
        exact scratch_not_output i (Fin.ext hv))).2
    · simpa only [core_output_slot] using (atape 213).trans rt
  · rw [←core_flag_slot,atape]
    exact rf

end NearCubicWires.RepairOrdinary.CloseoutRowsIntegerRound
