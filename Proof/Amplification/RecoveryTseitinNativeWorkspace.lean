import Proof.Amplification.RecoveryTseitinNativeReadOnly
import Proof.Circuits.DecompositionSourceBounds

/-! The repeated node workspace is bounded by actual writes. The original
raw counters, native source and accumulated formula remain unpadded. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def work (i : Fin 1335) : Prop := i≠0 ∧ i≠1 ∧ i≠1062 ∧ i≠1333
instance (i : Fin 1335) : Decidable (work i) := inferInstanceAs (Decidable (i≠0 ∧ i≠1 ∧ i≠1062 ∧ i≠1333))
def caps (cap : Nat) (i : Fin 1335) := if work i then cap else 0

theorem head_zero (pre out : List Bool) : ∀ i : Fin 1335,i≠1062 → i≠1333 → coldHeads pre out i=0 := by
  intro i
  refine Fin.addCases (m:=1099) (n:=236) (fun j hsrc _hout=>?_) (fun j _hsrc hout=>?_) i
  · have hj : j≠1062 := by
      intro he
      apply hsrc
      exact congrArg (Fin.castAdd 236) he
    simp only [coldHeads,Fin.addCases_left,heads,if_neg hj]
  · have hj : j≠234 := by
      intro he
      apply hout
      exact congrArg (Fin.natAdd 1099) he
    simp only [coldHeads,Fin.addCases_right,extraHeads,if_neg hj]
theorem input_blank (n index : Nat) (word out : List Bool) :
    ∀ i,work i → coldInput n index word out i=[] := by
  have small (j : Fin 10) (h0 : j≠0) (h1 : j≠1) : RecoveryTseitinReferences.input n index 0 0 j=[] := by
    fin_cases j <;> simp_all [RecoveryTseitinReferences.input]
  intro i
  refine Fin.addCases (m:=1099) (n:=236) (fun j hj=>?_) (fun j hj=>?_) i
  · have hsrc : j≠1062 := by
      intro he
      exact hj.2.2.1 (congrArg (Fin.castAdd 236) he)
    simp only [coldInput,Fin.addCases_left,input,if_neg hsrc]
    split_ifs with hlarge
    · unfold RecoveryTseitinReferences.coldInput
      split_ifs with hsmall
      · apply small
        · intro he
          have hv:=congrArg Fin.val he
          exact hj.1 (Fin.ext hv)
        · intro he
          have hv:=congrArg Fin.val he
          exact hj.2.1 (Fin.ext hv)
      · rfl
    · rfl
  · have hout : j≠234 := by
      intro he
      exact hj.2.2.2 (congrArg (Fin.natAdd 1099) he)
    simp only [coldInput,Fin.addCases_right,extraTapes,if_neg hout]
theorem scratch_support {s : Nat} (p : Machine 1335 s) (n index : Nat) (pre word out : List Bool)
    (fuel cap : Nat) (r : ExecutionReceipt 1335 s)
    (hr : runFrom p fuel ⟨p.start,coldHeads pre out,coldInput n index word out⟩=some r)
    (hcap : r.steps ≤ cap) : ∀ i,work i → (r.final.tapes i).length ≤ cap := by
  intro i hi
  have h:=DecompositionSource.one_tape_support p fuel _ r i 0 hr
    (by simp only [head_zero pre out i hi.2.2.1 hi.2.2.2,Nat.le_refl])
    (by simp only [input_blank n index word out i hi,List.length_nil,Nat.le_refl])
  exact h.trans (by simpa only [Nat.zero_add] using hcap)

end NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
