import Proof.PCP.PCPPNativeQueryStep

/-! Query-level selective reset. The original descriptor is rewound and
the old projection row can be erased; the live output and actual base/C/F
counters are excluded. Pure input support is proved before whole controls. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQueryReset
open LocalBitMultitape PCPPNativeQuery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def work (i : Fin 168) : Prop := i.val=1 ∨ (6 ≤ i.val ∧ i.val≠120)
def selected (i : Fin 168) := decide (i.val=0 ∨ i.val=1 ∨ (6 ≤ i.val ∧ i.val≠120))
def caps (G : ℕ) (i : Fin 169) := if i.val=1 ∨ (6 ≤ i.val ∧ i.val≠120) then G else 0
noncomputable def machine := MaskedReset.machine PCPPNativeQueryStep.machine selected
noncomputable def entry (bits queries : List Bool) (base C F G : ℕ) (out : List Bool) :=
  ZeroPadding.config (caps G) (Rewind.recording (PCPPNativeQueryStep.entry bits queries base C F out) 0)

theorem initial_head (out : List Bool) (i : Fin 168) (hi : selected i=true) : PCPPNativeQuery.heads 0 out i=0 := by
  have hs : i.val=0 ∨ work i := by simpa only [selected,work,decide_eq_true_eq] using hi
  have h5 : i≠5 := by intro h; subst i; simp [work] at hs
  by_cases hl : i.val < 122
  · let j : Fin 122 := ⟨i.val,hl⟩
    have he : i=j.castAdd 46 := Fin.ext rfl
    have hj5 : j≠5 := by intro h; apply h5; rw [he,h]; rfl
    rw [he]
    simp only [PCPPNativeQuery.heads,Fin.addCases_left,PCPPNativeNodeReusable.heads,hj5,ite_false]
    split_ifs <;> rfl
  · exact (cold_high [] [] 0 0 0 0 0 out i (by omega)).1

theorem initial_work (bits queries : List Bool) (base C F : ℕ) (out : List Bool)
    (i : Fin 168) (hi : work i) :
    (PCPPNativeQuery.data bits queries base base C F out i).length ≤ max queries.length (F+1) := by
  by_cases hl : i.val < 122
  · let j : Fin 122 := ⟨i.val,hl⟩
    have he : i=j.castAdd 46 := Fin.ext rfl
    rw [he]
    simp only [PCPPNativeQuery.data,Fin.addCases_left]
    have hwork : j.val=1 ∨ (6 ≤ j.val ∧ j.val≠120) := hi
    by_cases hj1 : j=1
    · change (PCPPNativeNodeReusable.data bits queries base base C F out j).length ≤ _
      rw [hj1]
      exact Nat.le_max_left queries.length (F+1)
    · have h1 : j.val≠1 := fun h => hj1 (Fin.ext h)
      have hlow : 6 ≤ j.val := by omega
      have h120 : j≠120 := by intro h; have hv := congrArg Fin.val h; omega
      have h0 : j≠0 := by intro h; subst j; omega
      have h2 : j≠2 := by intro h; subst j; omega
      have h3 : j≠3 := by intro h; subst j; omega
      have h4 : j≠4 := by intro h; subst j; omega
      have h5 : j≠5 := by intro h; subst j; omega
      simp only [PCPPNativeNodeReusable.data,h0,hj1,h2,h3,h4,h5,h120,ite_false]
      split_ifs <;> simp only [List.length_replicate] <;> omega
  · rw [(cold_high bits queries 0 base base C F out i (by omega)).2]
    exact Nat.zero_le _

def retainedSlots : Fin 6 → Fin 169 := ![0,2,3,4,5,120]
def retainedHeads (out : List Bool) : Fin 6 → ℕ := ![0,0,0,0,out.length,0]
def retainedData (bits : List Bool) (base C F : ℕ) (out : List Bool) : Fin 6 → List Bool :=
  ![bits,List.replicate base true,List.replicate base true,List.replicate C true,out,List.replicate F true]

end NearCubicWires.RepairOrdinary.PCPPNativeQueryReset
