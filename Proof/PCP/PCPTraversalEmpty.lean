import Proof.PCP.PCPTraversalFinish

/-! Actual empty-list branch: count-test, paid clearing, printing the empty
canonical field, and return to the unique raw-output tail. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def emptySlots : Fin 2 → Fin 128 := ![77,89]
def emptyLocal (cap : ℕ) : Fin 2 → List Bool :=
  ![ZeroPadding.pad cap (frame []),List.replicate cap false]
noncomputable def emptyOutput (cap log : ℕ) (tapes : Fin 128 → List Bool) :=
  install emptySlots (cleared emptySlots cap log tapes) (emptyLocal cap)

theorem empty_body (cap log : ℕ) (heads : Fin 128 → ℕ) (tapes : Fin 128 → List Bool)
    (hc : 1≤cap) (hw : WorkBound cap tapes) (hh : WorkingHeads heads)
    (hd : tapes 28=List.replicate cap true) (hl : tapes 127=List.replicate log false)
    (hhd : heads 28=0) :
    Path 1 35 (2*cap+10) heads tapes heads (emptyOutput cap log tapes) := by
  obtain ⟨a,ha,hah,hat,_⟩ := clear_run emptySlots (by decide) (by decide) (by decide) cap log heads tapes
    (by intro i; fin_cases i
        · exact hw 77 (by decide) (by decide)
        · exact hw 89 (by decide) (by decide)) hd hl
    (by intro i; fin_cases i
        · exact hh 77 (by decide) (by decide) (by decide) (by decide)
        · exact hh 89 (by decide) (by decide) (by decide) (by decide)) hhd
    (hh 127 (by decide) (by decide) (by decide) (by decide))
  obtain ⟨b,hb,hbh,hbt,_⟩ := (padded_printer_ready (frame []) cap hc).focus_at emptySlots (by decide)
    heads (cleared emptySlots cap log tapes)
    (by intro i; exact cleared_slot emptySlots (by decide) (by decide) (by decide) cap log tapes i)
    (by intro i; fin_cases i
        · exact hh 77 (by decide) (by decide) (by decide) (by decide)
        · exact hh 89 (by decide) (by decide) (by decide) (by decide))
  have hb' : runFrom (printer (frame []) 77 89).2 4
      (Composition.restart a.final (printer (frame []) 77 89).2.start)=some b := by
    have he : Composition.restart a.final (printer (frame []) 77 89).2.start=
        (⟨(printer (frame []) 77 89).2.start,heads,cleared emptySlots cap log tapes⟩ : Configuration 128 _) := by
      apply configuration_ext
      · rfl
      · exact hah
      · exact hat
    rw [he]
    exact hb
  have joined := Composition.run_join (clear emptySlots).2 (printer (frame []) 77 89).2
    (2*cap+4) 4 _ a b ha hb'
  have hj : runFrom emptyProgram.2 (2*cap+9) ⟨emptyProgram.2.start,heads,tapes⟩=
      some (Composition.joinedReceipt a b) := by
    have he : (2*cap+4)+1+4=2*cap+9 := by omega
    rw [he] at joined
    exact joined
  have hpath := packed_path 1 35 emptyProgram rfl (2*cap+9) heads tapes _
    ⟨Composition.joinedReceipt a b,hj,hbh,hbt⟩ (by intro q scanned; simp [next])
  have he : (2*cap+9)+1=2*cap+10 := by omega
  rw [he] at hpath
  exact hpath

theorem empty_output_other (cap log : ℕ) (tapes : Fin 128 → List Bool) (i : Fin 128)
    (hi : i≠77 ∧ i≠89 ∧ i≠28 ∧ i≠127) : emptyOutput cap log tapes i=tapes i := by
  apply Eq.trans (install_other emptySlots _ _ i ?_)
    (cleared_other emptySlots cap log tapes i ?_ (Ne.symm hi.2.2.1) (Ne.symm hi.2.2.2))
  all_goals
    intro j
    fin_cases j
    · exact Ne.symm hi.1
    · exact Ne.symm hi.2.1

theorem stable_empty (cap pos : ℕ) (source countWord rightStack continuation leftStack : List Bool)
    (heads : Fin 128 → ℕ) (tapes : Fin 128 → List Bool)
    (st : Stable cap source countWord pos rightStack continuation leftStack heads tapes)
    (count : CountAt cap 0 tapes) (hc : 1≤cap) :
    ∃ out,Path 0 35 (2*cap+12) heads tapes heads out ∧
      Stable cap source countWord pos rightStack continuation leftStack heads out ∧
      out 77=ZeroPadding.pad cap (frame []) := by
  obtain ⟨backing,_,hcount⟩ := count
  obtain ⟨log,hlogBound,hlog⟩ := st.clearLog
  have htest := test_path 0 backing heads tapes hcount
    (st.workingHeads 79 (by decide) (by decide) (by decide) (by decide))
  have hbody := empty_body cap log heads tapes hc st.work st.workingHeads st.capacityTape hlog st.capacityHead
  have hpath := htest.trans hbody
  let out := emptyOutput cap log tapes
  refine ⟨out,?_,?_,install_slot emptySlots (by decide) _ (emptyLocal cap) 0⟩
  · change Path 0 35 (2+(2*cap+10)) heads tapes heads out at hpath
    have he : 2+(2*cap+10)=2*cap+12 := by omega
    rw [he] at hpath
    exact hpath
  · have hwork : WorkBound cap out := by
      apply (st.work.clear emptySlots (by decide) (by decide) (by decide)).install emptySlots
      intro i _ _
      fin_cases i
      · change (ZeroPadding.pad cap (frame [])).length≤cap
        rw [ZeroPadding.pad_length]
        exact max_le le_rfl hc
      · change (List.replicate cap false).length≤cap
        simp only [List.length_replicate,le_refl]
    refine ⟨hwork,st.workingHeads,st.lowHeads,
      (empty_output_other cap log tapes 0 (by decide)).trans st.sourceTape,st.sourceHead,
      (empty_output_other cap log tapes 2 (by decide)).trans st.countTape,st.countHead,?_,?_,?_,?_,?_,?_⟩
    · exact (install_other emptySlots _ _ 28 (by decide)).trans
        (cleared_driver emptySlots (by decide) (by decide) (by decide) cap log tapes)
    · refine ⟨max log (cap+1),max_le hlogBound le_rfl,?_⟩
      exact (install_other emptySlots _ _ 127 (by decide)).trans
        (cleared_log emptySlots (by decide) (by decide) (by decide) cap log tapes)
    · obtain ⟨z,hz⟩ := st.right.zeros
      exact ⟨st.right.head,⟨z,(empty_output_other cap log tapes 80 (by decide)).trans hz⟩⟩
    · obtain ⟨z,hz⟩ := st.continuation.zeros
      exact ⟨st.continuation.head,⟨z,(empty_output_other cap log tapes 81 (by decide)).trans hz⟩⟩
    · obtain ⟨z,hz⟩ := st.left.zeros
      exact ⟨st.left.head,⟨z,(empty_output_other cap log tapes 82 (by decide)).trans hz⟩⟩
    · exact (empty_output_other cap log tapes 78 (by decide)).trans st.fresh

end NearCubicWires.RepairOrdinary.PCPTraversal
