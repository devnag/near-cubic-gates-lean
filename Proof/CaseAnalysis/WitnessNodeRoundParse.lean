import Proof.CaseAnalysis.WitnessNodeLoad

/-! The full checked node body runs in the shared stream bank. Its exact
descriptor, bounds, and all-input scratch support are the erase consumer's
only premises; no local configuration is reset for free. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeRound
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

@[simp] theorem node_output_slot : nodeSlots 747=(747 : Fin 755):=by decide
@[simp] theorem node_flag_slot : nodeSlots 745=(745 : Fin 755):=by decide
def scratchCore (i : Fin 744) : Fin 749:=⟨(scratchSlots i).val,scratch_small i⟩
theorem scratch_core (i : Fin 744) : nodeSlots (scratchCore i)=scratchSlots i:=Fin.ext rfl

structure Stored (cap w : ℕ) (left right out source : List Bool) (flag : Bool)
    (tapes : Fin 755 → List Bool) : Prop where
  descriptor : tapes 747=out
  common : ∀ i : Fin 4,tapes (nodeSlots ((NodeGuard.common i).castAdd 3))=
    ZeroPadding.pad cap (NodeGuard.shared w left right i)
  extra : ∀ i : Fin 6,tapes (i.natAdd 749)=NodeRound.extra cap source flag i
  scratch : ∀ i : Fin 744,(tapes (scratchSlots i)).length ≤ cap

noncomputable def parser:=RecoveryFocus.machine nodeSlots NodeReady.machine
theorem parse_run (w position : ℕ) (left right bits out source : List Bool) (flag : Bool)
    (hl : left.length=w) (hr : right.length=w) (hw : bits.length+1 ≤ w) : ∃ result,
    runFrom parser (NodeReady.budget w bits)
      (cfg parser.start (NodeReady.capacity w) w position left right bits out source flag)=some result ∧
      result.steps ≤ NodeReady.budget w bits ∧
      result.final.heads=heads (NodeBody.appended bits out) position ∧
      Stored (NodeReady.capacity w) w left right (NodeBody.appended bits out) source flag result.final.tapes ∧
      (readTapeBit (result.final.tapes 745) 0=true ↔ NodeMeaning.valid (value left) (value right) bits):=by
  obtain ⟨r,hrun,rs,rt,rh,rlocal,rf,rc⟩:=NodeReady.node_run w left right bits out hl hr hw
  obtain ⟨a,ha,_,asteps,ah,atape,keep⟩:=RecoveryFocus.dock nodeSlots
    (by intro i j h;exact Fin.ext (congrArg (fun i : Fin 755=>i.val) h)) NodeReady.machine _
    (heads out position) (data (NodeReady.capacity w) w left right bits out source flag) _
    (heads_node _ _ _ _ _ _ _) (data_node _ _ _ _ _ _ _ _) r hrun
  have outside (i : Fin 6) : ∀ j : Fin 749,nodeSlots j≠i.natAdd 749:=by
    intro j h
    have hv:=congrArg Fin.val h
    change j.val=749+i.val at hv
    omega
  have aextras (i : Fin 6) : a.final.tapes (i.natAdd 749)=extra (NodeReady.capacity w) source flag i:=
    ((keep (i.natAdd 749) (outside i)).2).trans (data_extra _ _ _ _ _ _ _ _ i)
  refine ⟨a,ha,asteps.trans_le rs,?_,?_,?_⟩
  · funext i
    refine Fin.addCases (m:=749) (n:=6) ?_ ?_ i
    · intro j
      change a.final.heads (nodeSlots j)=heads (NodeBody.appended bits out) position (nodeSlots j)
      rw [ah,heads_node (NodeReady.capacity w) w position left right bits (NodeBody.appended bits out),NodeReady.entry_heads]
      by_cases hj:j=747
      · subst j
        simpa only [ite_true] using rh
      · simpa only [if_neg hj] using (rlocal j hj).1
    · intro j
      rw [(keep (j.natAdd 749) (outside j)).1]
      have h0:(j.natAdd 749 : Fin 755)≠747:=by
        intro h
        have hv:=congrArg Fin.val h
        change 749+j.val=747 at hv
        omega
      simp only [heads,if_neg h0]
  · refine ⟨?_,?_,aextras,?_⟩
    · simpa only [node_output_slot] using (atape 747).trans rt
    · intro i
      exact (atape _).trans (rc i)
    · intro i
      rw [←scratch_core i,atape]
      exact (rlocal (scratchCore i) (by
        intro h
        have hv:=congrArg Fin.val h
        exact scratch_not_output i (Fin.ext hv))).2
  · rw [←node_flag_slot,atape]
    exact rf

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeRound
