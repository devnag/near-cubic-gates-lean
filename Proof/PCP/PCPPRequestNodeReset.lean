import Proof.PCP.PCPPRequestNodeEntry

/-! Paid reset of the complete node encoder preserves only the original
streaming source cursor. Its finite zero-padded scratch can then be erased. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeReset
open LocalBitMultitape RepairRepresentation ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 642) : Bool := decide (i≠0)
def caps (capacity : ℕ) (i : Fin 643) : ℕ := if i.val=0 then 0 else capacity
noncomputable def machine := MaskedReset.machine PCPPRequestNodeCold.machine selected
noncomputable def entry (capacity : ℕ) (source : List Bool) (pos : ℕ) :=
  ZeroPadding.config (caps capacity) (Rewind.recording (PCPPRequestNodeCold.entry source pos) 0)

theorem caps_old (capacity : ℕ) (i : Fin 642) :
    caps capacity (i.castAdd 1)=if selected i then capacity else 0 := by
  simp only [caps,Fin.val_castAdd,selected,Bool.decide_iff]
  by_cases h : i=0
  · subst i; rfl
  · simp [h,show i.val≠0 from fun hv => h (Fin.ext hv)]

theorem initial_head (source : List Bool) (pos : ℕ) (i : Fin 642) (hi : i≠0) :
    (PCPPRequestNodeCold.entry source pos).heads i=0 := by
  rw [PCPPRequestNodeCold.entry_heads]
  exact if_neg hi
theorem initial_tape (source : List Bool) (pos : ℕ) (i : Fin 642) (hi : i≠0) :
    (PCPPRequestNodeCold.entry source pos).tapes i=[] := by
  rw [PCPPRequestNodeCold.entry_tapes]
  exact if_neg hi

theorem reset_run {n : ℕ} (pre tail : List Bool) (node : BooleanNode n) (capacity : ℕ)
    (hcap : PCPPRequestNodeCold.budget node+1 ≤ capacity) :
    ∃ fuel ≤ 2*PCPPRequestNodeCold.budget node+2,∃ r,
      runFrom machine fuel (entry capacity (pre++PCPPRequestNodeSchema.native node++tail) pre.length)=some r ∧
      r.final.heads 0=pre.length+(PCPPRequestNodeSchema.native node).length ∧
      (∀ i : Fin 643,i≠0 → r.final.heads i=0) ∧
      r.final.tapes 0=pre++PCPPRequestNodeSchema.native node++tail ∧
      r.final.tapes 630=ZeroPadding.pad capacity (frame (encodeBooleanNode node).bits) ∧
      r.final.tapes 642=List.replicate capacity false ∧
      (∀ i : Fin 643,i≠0 → (r.final.tapes i).length=capacity) ∧ r.steps=fuel := by
  obtain ⟨source,hr,hs,h0,hh0,⟨padding,hout⟩,_,_,_⟩ := PCPPRequestNodeCold.cold_run pre tail node
  have hp := (prefix_of_run PCPPRequestNodeCold.machine _ _ source hr).1
  have hhead (i : Fin 642) (hi : selected i=true) : source.final.heads i ≤ source.steps := by
    have h := SelectiveReset.prefix_head hp i
    simpa only [initial_head _ _ i (of_decide_eq_true hi),Nat.zero_add] using h
  obtain ⟨base,hb,bf,bs,_⟩ := MaskedReset.reset_run PCPPRequestNodeCold.machine selected
    _ _ source hr hhead
  obtain ⟨r,hrun,rf,rs,_⟩ := ZeroPadding.run_config machine (caps capacity) _ _ base hb
  have support (i : Fin 642) (hi : i≠0) : (source.final.tapes i).length ≤ capacity := by
    have h := PCPSerializerReuse.tape_support PCPPRequestNodeCold.machine _ _ source hr i 0 0
      (by rw [initial_head _ _ i hi]) (by rw [initial_tape _ _ i hi]; simp)
    simp only [Nat.zero_add,Nat.max_eq_right (Nat.zero_le _)] at h
    omega
  have oldH (i : Fin 642) : r.final.heads (i.castAdd 1)=
      if selected i then 0 else source.final.heads i := by
    simp [rf,bf,ZeroPadding.config,SelectiveReset.finished,Rewind.config]
  have oldT (i : Fin 642) : r.final.tapes (i.castAdd 1)=
      ZeroPadding.pad (if selected i then capacity else 0) (source.final.tapes i) := by
    simp [rf,bf,ZeroPadding.config,SelectiveReset.finished,Rewind.config,caps_old]
  have logH : r.final.heads 642=0 := by rw [rf,bf]; rfl
  have logT : r.final.tapes 642=List.replicate capacity false := by
    rw [rf,bf]
    change ZeroPadding.pad capacity (List.replicate source.steps false)=_
    exact PCPSerializerReuse.pad_zeros capacity source.steps (by omega)
  refine ⟨2*source.steps+2,by omega,r,hrun,?_,?_,?_,?_,logT,?_,rs.trans bs⟩
  · exact (oldH 0).trans hh0
  · intro i hi
    refine Fin.addCases (m := 642) (n := 1) (motive := fun j => j≠0 → r.final.heads j=0)
      (fun j hj => ?_) (fun j _ => ?_) i hi
    · have hj0 : j≠0 := by intro he; subst j; exact hj rfl
      simpa [selected,hj0] using oldH j
    · fin_cases j; exact logH
  · have ht : r.final.tapes 0=source.final.tapes 0 := by simpa [selected] using oldT 0
    exact ht.trans h0
  · have ht : r.final.tapes 630=ZeroPadding.pad capacity (source.final.tapes 630) := oldT 630
    rw [ht,hout]
    apply DecompositionAtomReset.pad_trailing
    have h := support 630 (by decide)
    simpa only [hout,List.length_append,List.length_replicate] using h
  · intro i hi
    refine Fin.addCases (m := 642) (n := 1) (motive := fun j => j≠0 → (r.final.tapes j).length=capacity)
      (fun j hj => ?_) (fun j _ => ?_) i hi
    · have hj0 : j≠0 := by intro he; subst j; exact hj rfl
      rw [oldT]
      simp [selected,hj0,ZeroPadding.pad_length,max_eq_left (support j hj0)]
    · fin_cases j
      change (r.final.tapes 642).length=capacity
      rw [logT,List.length_replicate]

end NearCubicWires.RepairOrdinary.PCPPRequestNodeReset
