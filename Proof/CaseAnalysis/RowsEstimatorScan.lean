import Proof.CaseAnalysis.RowsEstimatorInput
import Proof.MachineModel.OrdinaryUnaryTemplate

/-! Paid counting of the original cut stream. A retained field-count template
separates cuts; the scanner reads every frame marker and payload transition.
The second output is the literal byte length needed by the outer framer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Scan
open LocalBitMultitape RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 4 7 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==6
  rule:=fun q bs=>if q.val=0 then
      some ⟨1,fun _=>none,![.stay,.right,.stay,.stay]⟩
    else if q.val=1 then
      if bs 0 then some ⟨2,![none,none,some true,none],![.stay,.stay,.right,.stay]⟩
      else some ⟨6,fun _=>none,fun _=>.stay⟩
    else if q.val=2 then
      if bs 1 then some ⟨3,fun _=>none,![.stay,.right,.stay,.stay]⟩
      else some ⟨5,fun _=>none,![.stay,.left,.stay,.stay]⟩
    else if q.val=3 then
      some ⟨if bs 0 then 4 else 2,![none,none,none,some true],![.right,.stay,.stay,.right]⟩
    else if q.val=4 then
      some ⟨3,![none,none,none,some true],![.right,.stay,.stay,.right]⟩
    else if q.val=5 then
      some ⟨if bs 1 then 5 else 1,fun _=>none,![.stay,if bs 1 then .left else .right,.stay,.stay]⟩
    else none

def cfg (q : Fin 7) (source : List Bool) (pos n j count : ℕ) : Configuration 4 7:=
  ⟨q,![pos,j,count,pos],![source,UnaryTemplate.tape n,
    List.replicate count true,List.replicate pos true]⟩

theorem bit_steps (pre tail : List Bool) (bit : Bool) (n j count : ℕ) :
    Timed machine 2 (cfg 3 (pre++true::bit::tail) pre.length n j count)
      (cfg 3 (pre++true::bit::tail) (pre.length+2) n j count):=by
  have h0:step machine (cfg 3 (pre++true::bit::tail) pre.length n j count)=
      some (cfg 4 (pre++true::bit::tail) (pre.length+1) n j count):=by
    simp [step,machine,cfg,Configuration.scanned,read_append]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
    · funext i;fin_cases i <;> simp [applyAction,List.replicate_add]
  have h1:step machine (cfg 4 (pre++true::bit::tail) (pre.length+1) n j count)=
      some (cfg 3 (pre++true::bit::tail) (pre.length+2) n j count):=by
    simp [step,machine,cfg]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply,Nat.add_assoc]
    · funext i;fin_cases i <;> simp [applyAction]
  exact (Timed.single (by rfl) h0).trans (Timed.single (by rfl) h1)

theorem delimiter_step (pre tail : List Bool) (n j count : ℕ) :
    step machine (cfg 3 (pre++false::tail) pre.length n j count)=
      some (cfg 2 (pre++false::tail) (pre.length+1) n j count):=by
  simp [step,machine,cfg,Configuration.scanned,read_append]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,List.replicate_add]

theorem field_timed (pre bits tail : List Bool) (n j count : ℕ) :
    Timed machine (frame bits).length
      (cfg 3 (pre++frame bits++tail) pre.length n j count)
      (cfg 2 (pre++frame bits++tail) (pre.length+(frame bits).length) n j count):=by
  induction bits generalizing pre with
  | nil=>simpa [frame] using Timed.single (by rfl) (delimiter_step pre tail n j count)
  | cons bit bits ih=>
    have h:=(bit_steps pre (frame bits++tail) bit n j count).trans
      (by simpa [List.append_assoc] using ih (pre++[true,bit]))
    have ht : 2+(2*bits.length+1)=(frame (bit::bits)).length:=by simp;omega
    have hp : pre.length+2+(2*bits.length+1)=pre.length+(frame (bit::bits)).length:=by simp;omega
    rw [ht,hp] at h
    simpa only [frame,List.cons_append,List.nil_append,List.append_assoc] using h

theorem field_start (source : List Bool) (pos n k count : ℕ) (hk:k<n) :
    step machine (cfg 2 source pos n (k+1) count)=
      some (cfg 3 source pos n (k+2) count):=by
  simp [step,machine,cfg,Configuration.scanned,UnaryTemplate.tape_mark n k hk]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply,Nat.add_assoc]
  · rfl

theorem fields_timed (pre tail : List Bool) (fields : List (List Bool))
    (n k count : ℕ) (hk:k+fields.length≤n) :
    Timed machine ((fields.flatMap frame).length+fields.length)
      (cfg 2 (pre++fields.flatMap frame++tail) pre.length n (k+1) count)
      (cfg 2 (pre++fields.flatMap frame++tail)
        (pre.length+(fields.flatMap frame).length) n (k+fields.length+1) count):=by
  induction fields generalizing pre k with
  | nil=>simpa using Timed.refl machine (cfg 2 (pre++tail) pre.length n (k+1) count)
  | cons bits fields ih=>
    have h0:=Timed.single (by rfl)
      (field_start (pre++frame bits++fields.flatMap frame++tail) pre.length n k count (by simp at hk;omega))
    have h1:=field_timed pre bits (fields.flatMap frame++tail) n (k+2) count
    have h2:=ih (pre++frame bits) (k+1) (by simp at hk;omega)
    have h:=(h0.trans (by simpa [List.append_assoc] using h1)).trans
      (by simpa [List.append_assoc,Nat.add_assoc] using h2)
    simpa [List.flatMap_cons,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem reset_zero (source : List Bool) (pos n count : ℕ) :
    step machine (cfg 5 source pos n 0 count)=some (cfg 1 source pos n 1 count):=by
  simp [step,machine,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem reset_timed (source : List Bool) (pos n j count : ℕ) (hj:j≤n) :
    Timed machine (j+1) (cfg 5 source pos n j count) (cfg 1 source pos n 1 count):=by
  induction j with
  | zero=>exact Timed.single (by rfl) (reset_zero source pos n count)
  | succ j ih=>
    have hs:step machine (cfg 5 source pos n (j+1) count)=some (cfg 5 source pos n j count):=by
      simp [step,machine,cfg,Configuration.scanned,UnaryTemplate.tape_mark n j (by omega)]
      apply configuration_ext
      · rfl
      · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
      · rfl
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (Timed.single (by rfl) hs).trans (ih (by omega))

theorem end_fields (source : List Bool) (pos n count : ℕ) :
    step machine (cfg 2 source pos n (n+1) count)=some (cfg 5 source pos n n count):=by
  simp [step,machine,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem group_start (source : List Bool) (pos n count : ℕ)
    (hs:readTapeBit source pos=true) :
    step machine (cfg 1 source pos n 1 count)=some (cfg 2 source pos n 1 (count+1)):=by
  simp [step,machine,cfg,Configuration.scanned,hs]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,List.replicate_add]

theorem group_timed (pre tail : List Bool) (fields : List (List Bool)) (n count : ℕ)
    (hn:fields.length=n) (hs:readTapeBit (pre++fields.flatMap frame++tail) pre.length=true) :
    Timed machine ((fields.flatMap frame).length+2*n+3)
      (cfg 1 (pre++fields.flatMap frame++tail) pre.length n 1 count)
      (cfg 1 (pre++fields.flatMap frame++tail)
        (pre.length+(fields.flatMap frame).length) n 1 (count+1)):=by
  have h0:=Timed.single (by rfl) (group_start _ pre.length n count hs)
  have h1:=fields_timed pre tail fields n 0 (count+1) (by omega)
  have h2:=Timed.single (by rfl) (end_fields (pre++fields.flatMap frame++tail)
    (pre.length+(fields.flatMap frame).length) n (count+1))
  have h3:=reset_timed (pre++fields.flatMap frame++tail)
    (pre.length+(fields.flatMap frame).length) n n (count+1) (by rfl)
  have h:=((h0.trans (by simpa only [hn,Nat.zero_add] using h1)).trans h2).trans h3
  convert h using 1
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Scan
