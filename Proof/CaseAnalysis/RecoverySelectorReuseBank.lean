import Proof.CaseAnalysis.RecoverySelectorBankOutput

/-! Reusable whole-selector backing: value, outer stack and retained index
are padded in the actual run. The selected rewind resets the consumed source
cursor; the graph append cursor and both count sentinels are retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorReuse
open LocalBitMultitape RepairRepresentation
open RecoveryBoundedSelectorLoop RecoveryBoundedSelectorFinish
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def caps (C : ℕ) (i : Fin 43):=if i=34 ∨ i=40 ∨ i=41 then C else 0
def selected (i : Fin 43):=decide (i=37)
def paddedData (index base C D value limit total : ℕ) (out source : List Bool) (i : Fin 43):=
  ZeroPadding.pad (caps C i) (data index base C D value limit total out source [] i)
def finalHeads (out : List Bool) : Fin 44→ℕ :=
  Fin.addCases (m:=43) (n:=1) (motive:=fun _=>ℕ) (heads out [] 0) (fun _=>0)
def finalData (index base C D value limit total L : ℕ) (out source : List Bool) : Fin 44→List Bool :=
  Fin.addCases (m:=43) (n:=1) (motive:=fun _=>List Bool)
    (paddedData index base C D value limit total out source) (fun _=>List.replicate L false)

theorem padded_after (index base C D value limit total z : ℕ) (out source : List Bool) (hz : z ≤ C) :
    (fun i=>ZeroPadding.pad (caps C i) (afterData index base C D value limit total z out source [] i))=
      paddedData index base C D value limit total out source := by
  funext i
  by_cases hi : i=40
  · subst i
    change ZeroPadding.pad C (List.replicate z false)=ZeroPadding.pad C []
    rw [pad_erased C z hz]
    rfl
  · simp only [afterData,if_neg hi,paddedData]

theorem reset_heads (out : List Bool) (pos : ℕ) :
    (fun i=>if selected i then 0 else heads out [] pos i)=heads out [] 0 := by
  funext i
  fin_cases i <;> rfl

theorem erased_small (base W : ℕ) (out : List Bool) (refs : List ℕ)
    (hc : refs.length ≤ W) (href : ∀ ref∈refs,ref ≤ W) :
    (folded base out refs).erased ≤ capacity W := by
  have h:=erased_bound false W refs.reverse ⟨base,0,0,out⟩
    (by intro ref hr; exact href ref (List.mem_reverse.mp hr))
  simp only [List.length_reverse,Nat.zero_add] at h
  have hm:=Nat.mul_le_mul_right (2*W+1) hc
  change (RecoveryBoundedNativeFoldLoop.State.iterate false refs.reverse ⟨base,0,0,out⟩).erased ≤ capacity W
  unfold capacity
  nlinarith [Nat.zero_le (W^2)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorReuse
