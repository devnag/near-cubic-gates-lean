import Proof.Amplification.RecoveryRawViewBodyTail

/-! The physical count reader gates the enclosing copy/check tail. A bad
count halts false with its actual unrepaired endpoint; a good count supplies
both the loop's unary driver and its bound. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewBody
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def countAnswer (x : State) (word : List Bool) (k : Nat) (bits : List Bool) :=
  (readCount x.limit (word.drop k)).any (fun pair=>clauseAnswer (copied (counted x pair.1) bits))
def countOutput (x : State) (word : List Bool) (k : Nat) (bits : List Bool) :=
  match readCount x.limit (word.drop k) with
  | none=>x
  | some (n,_)=>finished (copied (counted x n) bits)

theorem count_trace (x : State) (word : List Bool) (k : Nat) (bits : List Bool)
    (hx : x.Valid) (hz : x.count=0) (hs : x.inner.stream.source=frame word)
    (hp : x.inner.stream.pos=2*k) (hw : bits.length=x.width)
    (hf : x.outer.fields 0=frame bits) (hfalse : x.inner.stream.data.present=false) :
    ∃ n e,n ≤ countBudget x.width x.limit ∧
      Timed machine n (controlConfig (RecoveryCalls.code sizes 3) (x.cfg countMachine.start))
        (RecoveryCalls.stopped sizes e.heads e.tapes) ∧
      Result (countAnswer x word k bits) (countOutput x word k bits) e := by
  have hrun := count_retained_run x word k hz hs hp
  obtain ⟨first,hr,_,hc,hh,ht,hout⟩ := hrun
  cases hparse : readCount x.limit (word.drop k) with
  | none=>
    have hne : first.final.control≠3 := by
      intro he
      have hh := hc.mp he
      simp only [hparse,Option.isSome_none,Bool.false_eq_true] at hh
    have hn : next 3 first.final.control first.final.scanned=none := by
      change (if first.final.control.val=3 then some (4 : Fin 6) else none)=none
      apply if_neg
      intro he
      exact hne (Fin.ext he)
    have htrace := stop_receipt sizes programs 0 next 3 (3*x.limit+3) _ first hr hn
    obtain ⟨n,hn,h⟩ := htrace
    refine ⟨n,⟨0,first.final.heads,first.final.tapes⟩,?_,h,hh,?_,?_⟩
    · unfold countBudget
      omega
    · change first.final.tapes 28=_
      rw [ht,hfalse]
      simp only [countAnswer,hparse,Option.any_none]
    · simp only [countAnswer,hparse,Option.any_none,Bool.false_eq_true,IsEmpty.forall_iff]
  | some pair=>
    rcases pair with ⟨total,rest⟩
    obtain ⟨htotal,he⟩ := hout total rest hparse
    have hn : next 3 first.final.control first.final.scanned=some 4 := by
      change (if first.final.control.val=3 then some (4 : Fin 6) else none)=some 4
      rw [he]
      rfl
    have htrace := call_receipt sizes programs 0 next 3 4 (3*x.limit+3) _ first hr hn
    obtain ⟨n0,hn0,h0⟩ := htrace
    have htail := copy_trace (counted x total) bits (counted_valid x total hx htotal) hw hf
    obtain ⟨n1,e,hn1,h1,hresult⟩ := htail
    rw [he] at h0
    have h := h0.trans h1
    refine ⟨n0+n1,e,?_,h,?_⟩
    · change n1 ≤ copyBudget x.width x.limit at hn1
      unfold countBudget
      omega
    · simpa only [countAnswer,countOutput,hparse,Option.any_some] using hresult

end NearCubicWires.RepairOrdinary.RecoveryRawViewBody
