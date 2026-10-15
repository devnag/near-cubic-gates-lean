import Proof.PCP.PCPSerializerTapeSupport

/-! The actual serializer is run in retained finite zero padding, followed
by a paid reset of every local head except the two live stream cursors.
The source's arbitrary prefix and suffix lengths do not enter scratch bounds. -/
namespace NearCubicWires.RepairOrdinary.PCPSerializerReuse
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 128) : Bool := decide (i≠0 ∧ i≠2)
def caps (capacity : ℕ) (i : Fin 129) : ℕ := if i.val=0 ∨ i.val=2 then 0 else capacity
def machine {s : ℕ} (p : Machine 128 s) := MaskedReset.machine p selected

theorem caps_old (capacity : ℕ) (i : Fin 128) :
    caps capacity (i.castAdd 1)=if selected i then capacity else 0 := by
  simp only [caps,Fin.val_castAdd,selected,Bool.decide_iff]
  by_cases h0 : i=0
  · subst i; simp
  by_cases h2 : i=2
  · subst i; simp
  · simp [h0,h2,show i.val≠0 from fun h => h0 (Fin.ext h),show i.val≠2 from fun h => h2 (Fin.ext h)]

theorem pad_zeros (capacity n : ℕ) (hn : n ≤ capacity) :
    ZeroPadding.pad capacity (List.replicate n false)=List.replicate capacity false := by
  simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
  congr 1
  omega

theorem reset_run {s : ℕ} (p : Machine 128 s) (fuel capacity : ℕ)
    (c : Configuration 128 s) (source : ExecutionReceipt 128 s)
    (hr : runFrom p fuel c=some source)
    (hh : ∀ i,selected i=true → c.heads i=0)
    (ht : ∀ i,selected i=true → c.tapes i=[])
    (hcap : source.steps+1 ≤ capacity) :
    ∃ r,runFrom (machine p) (2*source.steps+2)
      (ZeroPadding.config (caps capacity) (Rewind.recording c 0))=some r ∧
      r.steps=2*source.steps+2 ∧
      (∀ i : Fin 128,r.final.heads (i.castAdd 1)=if selected i then 0 else source.final.heads i) ∧
      (∀ i : Fin 128,r.final.tapes (i.castAdd 1)=ZeroPadding.pad
        (if selected i then capacity else 0) (source.final.tapes i)) ∧
      (∀ i : Fin 128,selected i=true → (r.final.tapes (i.castAdd 1)).length=capacity) ∧
      r.final.heads 128=0 ∧ r.final.tapes 128=List.replicate capacity false := by
  have hhead (i : Fin 128) (hi : selected i=true) : source.final.heads i ≤ source.steps := by
    have h := SelectiveReset.prefix_head (prefix_of_run p fuel c source hr).1 i
    simpa only [hh i hi,Nat.zero_add] using h
  obtain ⟨base,hb,hbf,hbs,_⟩ := MaskedReset.reset_run p selected fuel c source hr hhead
  obtain ⟨r,hrun,hf,hs,_⟩ := ZeroPadding.run_config (machine p) (caps capacity) _ _ base hb
  have hsupp (i : Fin 128) (hi : selected i=true) : (source.final.tapes i).length ≤ capacity := by
    have h := tape_support p fuel c source hr i 0 0 (by rw [hh i hi]) (by rw [ht i hi]; simp)
    simp only [Nat.zero_add,Nat.max_eq_right (Nat.zero_le _)] at h
    exact h.trans hcap
  refine ⟨r,hrun,hs.trans hbs,?_,?_,?_,?_,?_⟩
  · intro i
    simp [hf,hbf,ZeroPadding.config,SelectiveReset.finished,Rewind.config]
  · intro i
    simp [hf,hbf,ZeroPadding.config,SelectiveReset.finished,Rewind.config,caps_old]
  · intro i hi
    simp [hf,hbf,ZeroPadding.config,SelectiveReset.finished,Rewind.config,caps_old,hi,
      ZeroPadding.pad_length,max_eq_left (hsupp i hi)]
  · rw [hf,hbf]
    change Fin.addCases (fun i => if selected i then 0 else source.final.heads i)
      (fun _ : Fin 1 => 0) ((0 : Fin 1).natAdd 128)=0
    rw [Fin.addCases_right]
  · rw [hf,hbf]
    change ZeroPadding.pad capacity (Fin.addCases source.final.tapes
      (fun _ : Fin 1 => List.replicate source.steps false) ((0 : Fin 1).natAdd 128))=_
    rw [Fin.addCases_right]
    exact pad_zeros capacity source.steps (by omega)

end NearCubicWires.RepairOrdinary.PCPSerializerReuse
