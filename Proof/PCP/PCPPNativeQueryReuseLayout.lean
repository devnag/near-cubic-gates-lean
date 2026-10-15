import Proof.PCP.PCPPNativeQueryReset

/-! Physical reusable query bank. The distinct actual G counter pays
clearing the old projection cache and all query parser work. C and F remain
the actual inner scalar/node capacities, preserved at their original slots. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQueryReusable
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def resetSlots (i : Fin 169) : Fin 171 := i.castAdd 2
def eraseSlots (i : Fin 165) : Fin 171 :=
  if i=0 then 1 else if i.val < 115 then ⟨i.val+5,by omega⟩ else ⟨i.val+6,by omega⟩
theorem erase_injective : Function.Injective eraseSlots := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [eraseSlots] at hv
  split_ifs at hv <;> simp_all only [Fin.ext_iff]
  all_goals omega
noncomputable def first := RecoveryFocus.machine resetSlots PCPPNativeQueryReset.machine
noncomputable def last := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 163)
noncomputable def machine := Composition.machine first last
def heads (out : List Bool) (i : Fin 171) := if i=5 then out.length else 0
def data (bits queries : List Bool) (base C F G : ℕ) (out : List Bool) (i : Fin 171) : List Bool :=
  if i=0 then bits else if i=1 then ZeroPadding.pad G queries
  else if i=2 ∨ i=3 then List.replicate base true else if i=4 then List.replicate C true
  else if i=5 then out else if i=120 then List.replicate F true else if i=169 then List.replicate G true
  else if i=170 then List.replicate (G+1) false else List.replicate G false
noncomputable def entry (bits queries : List Bool) (base C F G : ℕ) (out : List Bool) :=
  (⟨machine.start,heads out,data bits queries base C F G out⟩ : Configuration 171 _)

theorem reset_heads (out : List Bool) (i : Fin 168) :
    heads out (i.castAdd 3)=PCPPNativeQuery.heads 0 out i := by
  have h5 : i.castAdd 3=5 ↔ i=5 := by
    constructor
    · intro h; apply Fin.ext; exact congrArg (fun j : Fin 171 => j.val) h
    · intro h; subst i; rfl
  by_cases hi : i=5
  · subst i; rfl
  · rw [heads,if_neg (by simpa only [h5] using hi)]
    by_cases hl : i.val < 122
    · let j : Fin 122 := ⟨i.val,hl⟩
      have he : i=j.castAdd 46 := Fin.ext rfl
      have hj5 : j≠5 := by intro h; apply hi; rw [he,h]; rfl
      rw [he]
      simp only [PCPPNativeQuery.heads,Fin.addCases_left,PCPPNativeNodeReusable.heads,hj5,ite_false]
      split_ifs <;> rfl
    · exact (PCPPNativeQuery.cold_high [] [] 0 0 0 0 0 out i (by omega)).1.symm

theorem reset_data (bits queries : List Bool) (base C F G : ℕ) (out : List Bool)
    (hFG : F+1 ≤ G) (i : Fin 168) :
    data bits queries base C F G out (i.castAdd 3)=
      ZeroPadding.pad (PCPPNativeQueryReset.caps G (i.castAdd 1)) (PCPPNativeQuery.data bits queries base base C F out i) := by
  refine Fin.addCases (m := 122) (n := 46) (fun j => ?_) (fun j => ?_) i
  · simp only [PCPPNativeQuery.data,Fin.addCases_left]
    fin_cases j <;> simp [data,PCPPNativeQueryReset.caps,
      PCPPNativeNodeReusable.data,PCPPNativeNodeReusable.pad_zeros G F (by omega),
      PCPPNativeNodeReusable.pad_zeros G (F+1) hFG]
  · have away (k : Fin 171) (hk : k.val < 122 ∨ 168 ≤ k.val) : (j.natAdd 122).castAdd 3≠k := by
      intro h
      have hv : 122+j.val=k.val := congrArg (fun i : Fin 171 => i.val) h
      have hj := j.isLt
      omega
    have h0 := away 0 (Or.inl (by decide))
    have h1 := away 1 (Or.inl (by decide))
    have h2 := away 2 (Or.inl (by decide))
    have h3 := away 3 (Or.inl (by decide))
    have h4 := away 4 (Or.inl (by decide))
    have h5 := away 5 (Or.inl (by decide))
    have h120 := away 120 (Or.inl (by decide))
    have h169 := away 169 (Or.inr (by decide))
    have h170 := away 170 (Or.inr (by decide))
    have hcap : PCPPNativeQueryReset.caps G ((j.natAdd 122).castAdd 1)=G := by
      unfold PCPPNativeQueryReset.caps
      rw [if_pos (by right; simp only [Fin.val_castAdd,Fin.val_natAdd]; omega)]
    simp only [data,h0,h1,h2,h3,h4,h5,h120,h169,h170,or_self,ite_false,
      hcap,PCPPNativeQuery.data,Fin.addCases_right,PCPPNativeNodeReusable.pad_empty]

theorem reset_input (bits queries : List Bool) (base C F G : ℕ) (out : List Bool)
    (hFG : F+1 ≤ G) (i : Fin 169) :
    heads out (resetSlots i)=(PCPPNativeQueryReset.entry bits queries base C F G out).heads i ∧
      data bits queries base C F G out (resetSlots i)=(PCPPNativeQueryReset.entry bits queries base C F G out).tapes i := by
  refine Fin.addCases (m := 168) (n := 1) (fun j => ?_) (fun j => ?_) i
  · simp only [PCPPNativeQueryReset.entry,ZeroPadding.config,Rewind.recording,Rewind.config,
      PCPPNativeQueryStep.entry,Fin.addCases_left]
    exact ⟨reset_heads out j,reset_data bits queries base C F G out hFG j⟩
  · fin_cases j
    change 0=0 ∧ List.replicate G false=ZeroPadding.pad G []
    simp [ZeroPadding.pad]

end NearCubicWires.RepairOrdinary.PCPPNativeQueryReusable
