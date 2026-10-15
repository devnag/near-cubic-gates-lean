import Proof.Amplification.RecoveryBoundedNativeFoldLoop

/-! Full reverse fold output is the original postorder node suffix. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeFoldLoop
open LocalBitMultitape RepairRepresentation SourceInterfaces RecoveryBoundedNative RecoveryBoundedNativeFold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem iterate_meaning {n : ℕ} (conjunction : Bool) (refs : List ℕ) (a : State) :
    (a.iterate conjunction refs).acc=a.acc+refs.length ∧
    (a.iterate conjunction refs).out=a.out++(foldNodes (n:=n) conjunction a.acc refs).flatMap PCPPRequestNodeSchema.native := by
  induction refs generalizing a with
  | nil=>simp [State.iterate,foldNodes]
  | cons ref refs ih=>
    have h:=ih (a.next conjunction ref)
    simp only [State.iterate,foldNodes,List.length_cons]
    constructor
    · rw [h.1]
      dsimp only [State.next]
      omega
    · rw [h.2]
      cases conjunction <;>
        simp [State.next,emitted,tag,PCPPRequestNodeSchema.native,PCPPRequestNodeSchema.fields,List.append_assoc]

theorem original_fold_run {n : ℕ} (base W C : ℕ) (flag : Bool) (out pre : List Bool) (refs : List ℕ)
    (href : ∀ r∈refs,r ≤ W) (ha : base+refs.length ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    ∃ r, runFrom (machine true) (refs.length*(24*C+66)+refs.length+3)
      (configuration 0 true C flag pre refs.reverse ⟨base,0,0,out⟩ refs.length 1)=some r ∧
      r.steps ≤ refs.length*(24*C+66)+refs.length+3 ∧
      r.final.tapes 20=out++(foldNodes (n:=n) true base refs.reverse).flatMap PCPPRequestNodeSchema.native ∧
      r.final.tapes 25=List.replicate (base+refs.length) true ∧
      r.final.heads 31=pre.length ∧ r.final.heads 34=1 := by
  obtain ⟨r,hr,rf,rs⟩:=loop_run true W C refs.length flag pre refs.reverse ⟨base,0,0,out⟩
    (by simp) (by intro v hv; exact href v (List.mem_reverse.mp hv)) (by simpa using ha) hC
  have hm:=iterate_meaning (n:=n) true refs.reverse ⟨base,0,0,out⟩
  refine ⟨r,?_,?_,?_,?_,?_,?_⟩
  · simpa only [List.length_reverse] using hr
  · simpa only [List.length_reverse] using rs
  · rw [rf]
    change (State.iterate true refs.reverse ⟨base,0,0,out⟩).out=_
    exact hm.2
  · rw [rf]
    change List.replicate (State.iterate true refs.reverse ⟨base,0,0,out⟩).acc true=_
    rw [hm.1,List.length_reverse]
  · rw [rf]
    change (stack pre []).length=pre.length
    simp [stack,RecoveryBoundedNativeUnaryLoop.stackWords]
  · rw [rf]; rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeFoldLoop
