import Proof.MachineModel.UWitnessChoiceLoop

/-! Total bounded choices from the current framed witness cursor. Scratch
flags start blank; the copied output is physically rewound, and the source
cursor stops after exactly B choices on success or at its first missing bit. -/
namespace NearCubicWires.RepairOrdinary.UWitnessChoices
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def initial {s : ℕ} (state : Fin s) (w bound cap : ℕ) (source : List Bool) (cursor : ℕ) : Configuration 7 s :=
  ⟨state,![0,0,0,0,cursor,0,0],
    ![frame (binary w 0),frame (binary w bound),[],List.replicate cap false,source,[],[]]⟩
def rawBudget (w B : ℕ) := loopBudget w B+2
def consumed (B : ℕ) (bits : List Bool) := min B bits.length
def copied (B : ℕ) (bits : List Bool) := if B ≤ bits.length then frame (bits.take B) else Streaming.marks bits

theorem clear_prefix (w B cap : ℕ) (source : List Bool) (cursor : ℕ) :
    ∃ n,n ≤ 2 ∧ Timed raw n (initial raw.start w B cap source cursor)
      (atCheck w 0 B cap source [] cursor) := by
  have hc : step clear (initial 0 w B cap source cursor)=some (config 1 w 0 B cap false source [] cursor false) := by
    simp [step,clear,initial]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [applyAction,writeTapeBit]
  obtain ⟨r,hr,hf,_⟩ := (Timed.single (by rfl) hc).run (by rfl)
  obtain ⟨n,hn,h⟩ := call_receipt sizes programs 0 next 0 1 1 _ r hr (by simp [next])
  rw [hf] at h
  exact ⟨n,hn,h⟩

theorem raw_run (w B cap : ℕ) (pre bits : List Bool) (hb : B+1 < 2^w) (hcap : 2*w+1 ≤ cap) :
    ∃ r,runFrom raw (rawBudget w B) (initial raw.start w B cap (pre++frame bits) pre.length)=some r ∧
      r.final=done w (consumed B bits+1) B cap (decide (bits.length < B)) (decide (B ≤ bits.length))
        (pre++frame bits) (copied B bits) (pre.length+2*consumed B bits) ∧ r.steps ≤ rawBudget w B := by
  obtain ⟨n,hn,hclear⟩ := clear_prefix w B cap (pre++frame bits) pre.length
  by_cases hlen : B ≤ bits.length
  · obtain ⟨m,hm,hloop⟩ := valid_loop w 0 B cap pre (bits.take B) (bits.drop B) []
      (by simp [List.length_take,Nat.min_eq_left hlen]) hb hcap
    simp only [List.take_append_drop,List.nil_append] at hloop
    have htake : (bits.take B).length=B := by simp [List.length_take,Nat.min_eq_left hlen]
    rw [htake] at hm hloop
    have h := hclear.trans hloop
    obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [raw,done,RecoveryCalls.machine,RecoveryCalls.stopped])
    have hcost : n+m ≤ rawBudget w B := by dsimp [rawBudget]; omega
    have hmore := runFrom_moreFuel raw (n+m) (rawBudget w B-(n+m)) _ r hr
    rw [Nat.add_sub_of_le hcost] at hmore
    refine ⟨r,hmore,?_,by omega⟩
    simpa [consumed,copied,hlen,Nat.not_lt.mpr hlen,Nat.min_eq_left hlen] using hf
  · have hshort : bits.length < B := by omega
    obtain ⟨m,hm,hloop⟩ := short_loop w 0 B cap pre bits [] (by omega) hb hcap
    simp only [List.nil_append,Nat.zero_add] at hloop
    have h := hclear.trans hloop
    obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [raw,done,RecoveryCalls.machine,RecoveryCalls.stopped])
    have hcost : n+m ≤ rawBudget w B := by
      have hbnd : loopBudget w bits.length ≤ loopBudget w B :=
        Nat.mul_le_mul_right _ (by omega)
      dsimp only [rawBudget]
      omega
    have hmore := runFrom_moreFuel raw (n+m) (rawBudget w B-(n+m)) _ r hr
    rw [Nat.add_sub_of_le hcost] at hmore
    refine ⟨r,hmore,?_,by omega⟩
    simpa [consumed,copied,hlen,hshort,Nat.min_eq_right hshort.le] using hf

def selected (i : Fin 7) : Bool := decide (i.val=5)
noncomputable def machine := MaskedReset.machine raw selected
noncomputable def input (w B cap : ℕ) (source : List Bool) (cursor : ℕ) :=
  Rewind.recording (initial raw.start w B cap source cursor) 0
def finalHeads (cursor : ℕ) : Fin 8 → ℕ := ![0,0,0,0,cursor,0,0,0]
def output (w B cap : ℕ) (pre bits : List Bool) (g : ℕ) : Fin 8 → List Bool :=
  ![frame (binary w (consumed B bits+1)),frame (binary w B),[decide (bits.length < B)],
    List.replicate cap false,pre++frame bits,copied B bits,[decide (B ≤ bits.length)],List.replicate g false]
def budget (w B : ℕ) := 2*rawBudget w B+2

theorem prefix_run (w B cap : ℕ) (pre bits : List Bool) (hb : B+1 < 2^w) (hcap : 2*w+1 ≤ cap) :
    ∃ g r,runFrom machine (budget w B) (input w B cap (pre++frame bits) pre.length)=some r ∧
      r.final.tapes=output w B cap pre bits g ∧
      r.final.heads=finalHeads (pre.length+2*consumed B bits) ∧
      r.steps ≤ budget w B ∧ g ≤ rawBudget w B := by
  obtain ⟨base,hbRun,hbf,hbs⟩ := raw_run w B cap pre bits hb hcap
  have hhead : ∀ i : Fin 7,selected i=true → base.final.heads i ≤ base.steps := by
    intro i hi
    have he : i=(5 : Fin 7) := by apply Fin.ext; simpa [selected] using hi
    subst i
    have h := SelectiveReset.prefix_head (prefix_of_run raw (rawBudget w B) _ base hbRun).1 (5 : Fin 7)
    simpa [initial] using h
  obtain ⟨r,hr,hf,hs,_⟩ := MaskedReset.reset_run raw selected (rawBudget w B) _ base hbRun hhead
  have ht : 2*base.steps+2 ≤ budget w B := by dsimp [budget]; omega
  have hmore := runFrom_moreFuel machine (2*base.steps+2) (budget w B-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le ht] at hmore
  refine ⟨base.steps,r,hmore,?_,?_,by omega,hbs⟩
  · funext i
    fin_cases i <;> simp [hf,hbf,SelectiveReset.finished,Rewind.config,done,RecoveryCalls.stopped,output,Fin.addCases]
  · funext i
    fin_cases i <;> simp [hf,hbf,SelectiveReset.finished,Rewind.config,done,RecoveryCalls.stopped,
      selected,finalHeads,Fin.addCases]

end NearCubicWires.RepairOrdinary.UWitnessChoices
