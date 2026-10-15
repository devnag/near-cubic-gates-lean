import Proof.PCP.PCPTraversalSubtree

/-! The sole raw-output write in the serializer: node35 physically clears
its copy log, node36 copies the canonical field onto the still-fresh tape78,
and the controller pays the stopping transition. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def finalSlots : Fin 3 → Fin 128 := ![77,78,97]
def finalLocal (cap : ℕ) (bits : List Bool) : Fin 3 → List Bool :=
  ![ZeroPadding.pad cap (frame bits),bits,List.replicate cap false]
noncomputable def finalOutput (cap log : ℕ) (bits : List Bool) (tapes : Fin 128 → List Bool) :=
  install finalSlots (cleared ![97] cap log tapes) (finalLocal cap bits)

theorem final_ready (cap : ℕ) (bits : List Bool) (hc : bits.length≤cap) :
    ReadyRun Streaming.machine (4*bits.length+2)
      ![ZeroPadding.pad cap (frame bits),[],List.replicate cap false] (finalLocal cap bits) := by
  obtain ⟨base,hbase,hfinal,hsteps,_⟩ := Streaming.copy_run bits
  obtain ⟨r,hr,hf,hs,_⟩ := ZeroPadding.run_config Streaming.machine ![cap,0,cap] _ _ base hbase
  refine ⟨r,?_,?_,?_,hs.trans hsteps⟩
  · have he : ZeroPadding.config ![cap,0,cap]
        (initialConfiguration Streaming.machine (fun t => if t.val=0 then frame bits else []))=
        initialConfiguration Streaming.machine ![ZeroPadding.pad cap (frame bits),[],List.replicate cap false] := by
      apply configuration_ext
      · rfl
      · rfl
      · funext i
        fin_cases i <;> simp [ZeroPadding.config,initialConfiguration,ZeroPadding.pad]
    rw [he] at hr
    exact hr
  · rw [hf,hfinal]
    funext i
    fin_cases i
    · rfl
    · change ZeroPadding.pad 0 bits=bits
      simp only [ZeroPadding.pad,Nat.zero_sub,List.replicate_zero,List.append_nil]
    · change ZeroPadding.pad cap (List.replicate bits.length false)=List.replicate cap false
      simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
      congr 1
      omega
  · intro i
    rw [hf,hfinal]
    simp only [ZeroPadding.config,Streaming.finished,Streaming.config,ite_self]

theorem final_output_result (cap log : ℕ) (bits : List Bool) (tapes : Fin 128 → List Bool) :
    finalOutput cap log bits tapes 77=ZeroPadding.pad cap (frame bits) ∧
    finalOutput cap log bits tapes 78=bits :=
  ⟨install_slot finalSlots (by decide) _ (finalLocal cap bits) 0,
   install_slot finalSlots (by decide) _ (finalLocal cap bits) 1⟩

theorem final_output_other (cap log : ℕ) (bits : List Bool) (tapes : Fin 128 → List Bool)
    (i : Fin 128) (hi : i≠77 ∧ i≠78 ∧ i≠97 ∧ i≠28 ∧ i≠127) :
    finalOutput cap log bits tapes i=tapes i := by
  apply Eq.trans (install_other finalSlots _ _ i ?_) (cleared_other ![97] cap log tapes i ?_ (Ne.symm hi.2.2.2.1) (Ne.symm hi.2.2.2.2))
  · intro j
    fin_cases j
    · exact Ne.symm hi.1
    · exact Ne.symm hi.2.1
    · exact Ne.symm hi.2.2.1
  · intro j
    fin_cases j
    exact Ne.symm hi.2.2.1

theorem final_path (cap pos : ℕ) (source countWord rightStack continuation leftStack bits : List Bool)
    (heads : Fin 128 → ℕ) (tapes : Fin 128 → List Bool)
    (st : Stable cap source countWord pos rightStack continuation leftStack heads tapes)
    (hc : 2*bits.length+1≤cap) (hresult : tapes 77=ZeroPadding.pad cap (frame bits)) :
    ∃ fuel≤2*cap+4*bits.length+8,∃ out,
      Timed machine fuel (atCall 35 heads tapes) (RecoveryCalls.stopped sizes heads out) ∧
      out 77=ZeroPadding.pad cap (frame bits) ∧ out 78=bits ∧
      out 0=source ∧ out 2=countWord ∧ WorkBound cap out := by
  obtain ⟨log,_,hlog⟩ := st.clearLog
  have hclear := clear_path 35 36 ![97] rfl (by intro q scanned; simp [next]) (by decide)
    (by decide) (by decide) cap log heads tapes
    (by intro i; fin_cases i; exact st.work 97 (by decide) (by decide)) st.capacityTape hlog
    (by intro i; fin_cases i; exact st.workingHeads 97 (by decide) (by decide) (by decide) (by decide))
    st.capacityHead (st.workingHeads 127 (by decide) (by decide) (by decide) (by decide))
  obtain ⟨r,hr,hrh,hrt,_⟩ := (final_ready cap bits (by omega)).focus_at finalSlots (by decide) heads
    (cleared ![97] cap log tapes)
    (by intro i; fin_cases i
        · exact (cleared_other ![97] cap log tapes 77 (by decide) (by decide) (by decide)).trans hresult
        · exact (cleared_other ![97] cap log tapes 78 (by decide) (by decide) (by decide)).trans st.fresh
        · exact cleared_slot ![97] (by decide) (by decide) (by decide) cap log tapes 0)
    (by intro i; fin_cases i
        · exact st.workingHeads 77 (by decide) (by decide) (by decide) (by decide)
        · exact st.workingHeads 78 (by decide) (by decide) (by decide) (by decide)
        · exact st.workingHeads 97 (by decide) (by decide) (by decide) (by decide))
  obtain ⟨n,hn,hstop⟩ := stop_receipt sizes programs 37 next 36 (4*bits.length+2)
    (RecoveryCalls.restarted (programs 36) heads (cleared ![97] cap log tapes)) r hr (by simp [next])
  rw [hrh,hrt] at hstop
  obtain ⟨m,hm,hstart⟩ := hclear
  let out := finalOutput cap log bits tapes
  refine ⟨m+n,by omega,out,hstart.trans hstop,(final_output_result cap log bits tapes).1,
    (final_output_result cap log bits tapes).2,
    (final_output_other cap log bits tapes 0 (by decide)).trans st.sourceTape,
    (final_output_other cap log bits tapes 2 (by decide)).trans st.countTape,?_⟩
  apply (st.work.clear ![97] (by decide) (by decide) (by decide)).install finalSlots
  intro i _ _
  fin_cases i
  · change (ZeroPadding.pad cap (frame bits)).length≤cap
    rw [ZeroPadding.pad_length,frame_length]
    exact max_le le_rfl hc
  · change bits.length≤cap
    omega
  · change (List.replicate cap false).length≤cap
    simp only [List.length_replicate,le_refl]

end NearCubicWires.RepairOrdinary.PCPTraversal
