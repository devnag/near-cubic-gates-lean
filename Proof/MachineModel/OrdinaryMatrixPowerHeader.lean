import Proof.MachineModel.OrdinaryMatrixMarksAppend

/-! Physically print natWord(2^d) and its exact finite length driver from
one retained unary d. The two scans pay every header bit and reset all heads. -/
namespace NearCubicWires.RepairOrdinary.MatrixPowerHeader
open LocalBitMultitape RecoveryExecution SignedSortKey RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 3 7 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==6
  rule := fun q scan => if q.val=0 then
      some ⟨1,![none,none,some false],![.right,.stay,.right]⟩
    else if q.val=1 then
      some ⟨if scan 0 then 1 else 2,![none,some true,some true],
        ![if scan 0 then .right else .stay,.right,.right]⟩
    else if q.val=2 then
      some ⟨3,![none,some false,some true],![.left,.right,.right]⟩
    else if q.val=3 then
      some ⟨if scan 0 then 3 else 4,fun _ => none,![if scan 0 then .left else .right,.stay,.stay]⟩
    else if q.val=4 then
      some ⟨if scan 0 then 4 else 5,![none,some (!scan 0),some true],
        ![if scan 0 then .right else .stay,.right,.right]⟩
    else if q.val=5 then
      some ⟨6,![none,none,some false],fun _ => .stay⟩
    else none

def growing (n : ℕ) := false :: List.replicate n true

def cfg (q : Fin 7) (d h : ℕ) (out : List Bool) : Configuration 3 7 :=
  ⟨q,![h,out.length,out.length+1],![UnaryTemplate.tape d,out,growing out.length]⟩
def word (d : ℕ) := List.replicate (d+1) true++[false]++List.replicate d false++[true]
def input (d : ℕ) : Fin 3 → List Bool := ![UnaryTemplate.tape d,[],[]]
def final (d : ℕ) : Configuration 3 7 :=
  ⟨6,![d+1,(word d).length,(word d).length+1],![UnaryTemplate.tape d,word d,UnaryTemplate.tape (word d).length]⟩

@[simp] theorem word_length (d : ℕ) : (word d).length=2*d+3 := by simp [word]; omega

theorem growing_write (n : ℕ) : writeTapeBit (growing n) (n+1) true=growing (n+1) := by
  simpa [growing,List.replicate_add,List.append_assoc] using Streaming.write_append (growing n) true

theorem emit_step (q q' : Fin 7) (d h : ℕ) (out : List Bool) (bit : Bool) (move : HeadMove)
    (hr : raw.rule q (cfg q d h out).scanned=some ⟨q',![none,some bit,some true],![move,.right,.right]⟩) :
    step raw (cfg q d h out)=some (cfg q' d (HeadMove.apply move h) (out++[bit])) := by
  change Option.map (applyAction (cfg q d h out)) (raw.rule q (cfg q d h out).scanned)=_
  rw [hr]
  simp only [Option.map_some,Option.some.injEq]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,cfg,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,cfg,Streaming.write_append,growing_write]

theorem start_step (d : ℕ) : step raw (initialConfiguration raw (input d))=some (cfg 1 d 1 []) := by
  simp [step,raw,input,initialConfiguration]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem true_step (d k : ℕ) (hk : k<d) :
    step raw (cfg 1 d (k+1) (List.replicate k true))=some (cfg 1 d (k+2) (List.replicate (k+1) true)) := by
  have h := emit_step 1 1 d (k+1) (List.replicate k true) true .right
    (by simp [raw,cfg,Configuration.scanned,UnaryTemplate.tape_mark d k hk])
  simpa [HeadMove.apply,List.replicate_add] using h

theorem extra_step (d : ℕ) : step raw (cfg 1 d (d+1) (List.replicate d true))=
    some (cfg 2 d (d+1) (List.replicate (d+1) true)) := by
  have h := emit_step 1 2 d (d+1) (List.replicate d true) true .stay
    (by simp [raw,cfg,Configuration.scanned])
  simpa [HeadMove.apply,List.replicate_add] using h

theorem true_prefix (d k rem : ℕ) (he : k+rem=d) :
    Timed raw (rem+1) (cfg 1 d (k+1) (List.replicate k true))
      (cfg 2 d (d+1) (List.replicate (d+1) true)) := by
  induction rem generalizing k with
  | zero =>
    have hk : k=d := by omega
    subst k
    exact Timed.single (by rfl) (extra_step d)
  | succ rem ih =>
    have h := (Timed.single (by rfl) (true_step d k (by omega))).trans (ih (k+1) (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem delimiter_step (d : ℕ) : step raw (cfg 2 d (d+1) (List.replicate (d+1) true))=
    some (cfg 3 d d (List.replicate (d+1) true++[false])) := by
  have h := emit_step 2 3 d (d+1) (List.replicate (d+1) true) false .left (by rfl)
  simpa [HeadMove.apply] using h

theorem left_step (d k : ℕ) (hk : k<d) (out : List Bool) :
    step raw (cfg 3 d (k+1) out)=some (cfg 3 d k out) := by
  simp [step,raw,cfg,Configuration.scanned,UnaryTemplate.tape_mark d k hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem left_stop (d : ℕ) (out : List Bool) :
    step raw (cfg 3 d 0 out)=some (cfg 4 d 1 out) := by
  simp [step,raw,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem return_prefix (d k : ℕ) (hk : k≤d) (out : List Bool) :
    Timed raw (k+1) (cfg 3 d k out) (cfg 4 d 1 out) := by
  induction k with
  | zero => exact Timed.single (by rfl) (left_stop d out)
  | succ k ih =>
    have h := (Timed.single (by rfl) (left_step d k (by omega) out)).trans (ih (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem false_step (d k : ℕ) (hk : k<d) (pre : List Bool) :
    step raw (cfg 4 d (k+1) (pre++List.replicate k false))=
      some (cfg 4 d (k+2) (pre++List.replicate (k+1) false)) := by
  have h := emit_step 4 4 d (k+1) (pre++List.replicate k false) false .right
    (by simp [raw,cfg,Configuration.scanned,UnaryTemplate.tape_mark d k hk])
  simpa [HeadMove.apply,List.replicate_add,List.append_assoc] using h

theorem top_step (d : ℕ) (pre : List Bool) :
    step raw (cfg 4 d (d+1) (pre++List.replicate d false))=
      some (cfg 5 d (d+1) (pre++List.replicate d false++[true])) := by
  exact emit_step 4 5 d (d+1) (pre++List.replicate d false) true .stay
    (by simp [raw,cfg,Configuration.scanned])

theorem false_prefix (d k rem : ℕ) (he : k+rem=d) (pre : List Bool) :
    Timed raw (rem+1) (cfg 4 d (k+1) (pre++List.replicate k false))
      (cfg 5 d (d+1) (pre++List.replicate d false++[true])) := by
  induction rem generalizing k with
  | zero =>
    have hk : k=d := by omega
    subst k
    exact Timed.single (by rfl) (top_step d pre)
  | succ rem ih =>
    have h := (Timed.single (by rfl) (false_step d k (by omega) pre)).trans (ih (k+1) (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem finish_step (d : ℕ) : step raw (cfg 5 d (d+1) (word d))=some (final d) := by
  have hw : writeTapeBit (growing (word d).length) ((word d).length+1) false=UnaryTemplate.tape (word d).length := by
    simpa [growing,UnaryTemplate.tape] using Streaming.write_append (growing (word d).length) false
  simp only [word_length] at hw
  simp [step,raw,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,final,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,final,hw]

theorem raw_run (d : ℕ) : ∃ actual,
    run raw (3*d+6) (input d)=some actual ∧ actual.final=final d ∧ actual.steps=3*d+6 := by
  have h0 := Timed.single (by rfl) (start_step d)
  have h1 := true_prefix d 0 d (by omega)
  have h2 := Timed.single (by rfl) (delimiter_step d)
  have h3 := return_prefix d d (by omega) (List.replicate (d+1) true++[false])
  have h4 := false_prefix d 0 d (by omega) (List.replicate (d+1) true++[false])
  have h5 := Timed.single (by rfl) (finish_step d)
  simp only [List.replicate_zero,List.append_nil,Nat.zero_add] at h1 h4
  change Timed raw (d+1) _ (cfg 5 d (d+1) (word d)) at h4
  have h := h0.trans (h1.trans (h2.trans (h3.trans (h4.trans h5))))
  have ht : 1+((d+1)+(1+((d+1)+((d+1)+1))))=3*d+6 := by omega
  rw [ht] at h
  exact h.run (by rfl)

def machine := Rewind.machine raw
def resetInput (d : ℕ) : Fin 4 → List Bool := ![UnaryTemplate.tape d,[],[],[]]

theorem word_eq (d : ℕ) : word d=natWord (2^d) := by
  have hb : natBitLength (2^d)=d+1 := by simp [natBitLength,Nat.log_pow]
  have hv : RadixSemantics.value (List.replicate d false++[true])=2^d := by
    simp [RadixSemantics.value_append,RadixSemantics.value]
  have he := BoundedCounter.binary_of_value (List.replicate d false++[true])
  simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil,hv] at he
  simp [word,WilliamsInputHeader.natWord_eq,hb,he,List.append_assoc]

theorem header_run (d : ℕ) : ∃ actual,
    run machine (6*d+14) (resetInput d)=some actual ∧
    actual.final.tapes 0=UnaryTemplate.tape d ∧ actual.final.tapes 1=natWord (2^d) ∧
    actual.final.tapes 2=UnaryTemplate.tape (2*d+3) ∧
    (∀ i,actual.final.heads i=0) ∧ actual.steps=6*d+14 := by
  obtain ⟨base,hb,bf,bs⟩ := raw_run d
  obtain ⟨actual,hr,rt,rh,rs,_⟩ := Rewind.reset_run raw _ _ base hb
  have ht : 2*base.steps+2=6*d+14 := by omega
  rw [ht] at hr rs
  have hi : (Fin.addCases (motive := fun _ : Fin (3+1) => List Bool) (input d) (fun _ : Fin 1 => []))=resetInput d := by
    funext i; fin_cases i <;> rfl
  rw [hi] at hr
  refine ⟨actual,hr,(rt 0).trans (by rw [bf]; rfl),?_,?_,rh,rs⟩
  · exact (rt 1).trans (by rw [bf]; exact word_eq d)
  · exact (rt 2).trans (by rw [bf]; simp [final])

end NearCubicWires.RepairOrdinary.MatrixPowerHeader
