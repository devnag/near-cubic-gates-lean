import Proof.Amplification.RecoveryTseitinStream

/-! Allocate the tautology bank from its actual unary capacity. The output
cursor and repetition count are retained while the full blank workspace is
physically swept and rewound. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinTautology.Cold
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open RecoveryTseitinKernel VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def workSlot (i : Fin 236) : Fin 242 :=
  if i.val<234 then ⟨i.val+5,by omega⟩ else if i.val=234 then 0 else 240
def slots : Fin 238→Fin 242 := Fin.addCases (m:=237) (n:=1) (motive:=fun _=>Fin 242)
  (Fin.addCases (m:=236) (n:=1) (motive:=fun _=>Fin 242) workSlot (fun _ : Fin 1=>3)) (fun _ : Fin 1=>4)
theorem work_injective : Function.Injective workSlot := by
  intro i j he
  have h:=congrArg Fin.val he
  have hi:=i.isLt
  have hj:=j.isLt
  apply Fin.ext
  dsimp only [workSlot] at h
  split_ifs at h <;> dsimp at h <;> omega
theorem slots_value (i : Fin 238) : (slots i).val=
    if i.val<234 then i.val+5 else if i.val=234 then 0 else
    if i.val=235 then 240 else if i.val=236 then 3 else 4 := by
  refine Fin.addCases (m:=237) (n:=1) (fun a=>?_) (fun a=>?_) i
  · refine Fin.addCases (m:=236) (n:=1) (fun b=>?_) (fun b=>?_) a
    · simp only [slots,Fin.addCases_left,Fin.val_castAdd,workSlot]
      split_ifs <;> simp_all <;> omega
    · fin_cases b; rfl
  · fin_cases a; rfl
theorem injective : Function.Injective slots := by
  intro i j he
  have h:=congrArg Fin.val he
  rw [slots_value,slots_value] at h
  have hi:=i.isLt
  have hj:=j.isLt
  apply Fin.ext
  split_ifs at h <;> omega

noncomputable def bankMachine := RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 236)
def bankInput (cap count : Nat) (out : List Bool) : Fin 242→List Bool := fun i=>
  if i=3 then List.replicate cap true else if i=239 then out else
  if i=241 then CompareMachine.word count else []
def bankHeads (out : List Bool) : Fin 242→Nat := fun i=>if i=239 then out.length else 0
def initial (cap : Nat) : Fin 239→List Bool := fun i=>
  if i=1 ∨ i=2 then [] else if i=3 then List.replicate cap true else
  if i=4 then List.replicate (cap+1) false else List.replicate cap false
def bankOutput (cap count : Nat) (out : List Bool) : Fin 242→List Bool :=
  Fin.addCases (m:=241) (n:=1) (motive:=fun _=>List Bool)
    (input (initial cap) out cap) (fun _ : Fin 1=>CompareMachine.word count)

theorem initial_valid (cap : Nat) (hc : 1≤cap) : Valid cap 0 (initial cap) := by
  refine ⟨?_,rfl,rfl,?_⟩
  · change List.replicate cap false=ZeroPadding.pad cap [false]
    simp only [ZeroPadding.pad,List.length_singleton]
    rw [←List.replicate_one,←List.replicate_add]
    congr 1
    omega
  · intro i hi
    have h1 : i≠1 := by intro he; subst i; contradiction
    have h2 : i≠2 := by intro he; subst i; contradiction
    have h3 : i≠3 := by intro he; subst i; contradiction
    have h4 : i≠4 := by intro he; subst i; contradiction
    simp [initial,h1,h2,h3,h4]

theorem bank_run (cap count : Nat) (out : List Bool) : ∃ r,
    runFrom bankMachine (2*cap+4) ⟨bankMachine.start,bankHeads out,bankInput cap count out⟩=some r ∧
      r.final.heads=bankHeads out ∧ r.final.tapes=bankOutput cap count out ∧ r.steps≤2*cap+4 := by
  obtain ⟨base,hb,bt,bh,bs⟩ := RecoveryScratchErase.erase_ready cap 0 (fun _ : Fin 236=>[])
    (by intro i; simp)
  obtain ⟨r,hr,_rc,rs,rh,rt,ro⟩ := RecoveryFocus.dock slots injective
    (RecoveryScratchErase.resetMachine 236) (2*cap+4) (bankHeads out) (bankInput cap count out) _
    (by
      intro i
      change bankHeads out (slots i)=0
      have hv:=slots_value i
      have hi:=i.isLt
      have hn : slots i≠239 := by intro he; rw [he] at hv; split_ifs at hv <;> omega
      simp [bankHeads,hn])
    (by
      intro i
      refine Fin.addCases (m:=237) (n:=1) (fun a=>?_) (fun a=>?_) i
      · refine Fin.addCases (m:=236) (n:=1) (fun b=>?_) (fun b=>?_) a
        · simp only [slots,Fin.addCases_left,initialConfiguration]
          have hi:=b.isLt
          have hn (i : Fin 242) (he : i=3 ∨ i=239 ∨ i=241) : workSlot b≠i := by
            intro h
            have hv:=congrArg Fin.val h
            dsimp only [workSlot] at hv
            rcases he with he|he|he <;> subst i <;> split_ifs at hv <;> dsimp at hv <;> omega
          simp [bankInput,hn 3 (by simp),hn 239 (by simp),hn 241 (by simp)]
        · fin_cases b; rfl
      · fin_cases a; rfl) base hb
  have kept (i : Fin 242) (h1 : i=1 ∨ i=2 ∨ i=239 ∨ i=241) :
      r.final.heads i=bankHeads out i ∧ r.final.tapes i=bankInput cap count out i := by
    apply ro
    intro j he
    have hv:=slots_value j
    have hj:=j.isLt
    rw [he] at hv
    rcases h1 with h1|h1|h1|h1 <;> subst i <;> split_ifs at hv <;> omega
  have result (i : Fin 238) : r.final.heads (slots i)=0 ∧
      r.final.tapes (slots i)=bankOutput cap count out (slots i) := by
    refine ⟨(rh i).trans (bh i),?_⟩
    rw [rt,bt]
    refine Fin.addCases (m:=237) (n:=1) (fun a=>?_) (fun a=>?_) i
    · refine Fin.addCases (m:=236) (n:=1) (fun b=>?_) (fun b=>?_) a
      · simp only [slots,Fin.addCases_left]
        by_cases hb : b.val<234
        · have hs : workSlot b=((⟨b.val+5,by omega⟩ : Fin 239).castAdd 2).castAdd 1 := by simp [workSlot,hb]
          rw [hs]
          simp only [bankOutput,input,Fin.addCases_left]
          simp [initial,Fin.ext_iff]
        · have hi:=b.isLt
          simp [workSlot,hb]
          split <;> rfl
      · fin_cases b; rfl
    · fin_cases a; rfl
  have all (i : Fin 242) : r.final.heads i=bankHeads out i ∧
      r.final.tapes i=bankOutput cap count out i := by
    match i with
    | ⟨0,_⟩ => exact result (((234 : Fin 236).castAdd 1).castAdd 1)
    | ⟨1,_⟩ => exact kept 1 (by simp)
    | ⟨2,_⟩ => exact kept 2 (by simp)
    | ⟨3,_⟩ => exact result (((0 : Fin 1).natAdd 236).castAdd 1)
    | ⟨4,_⟩ => exact result ((0 : Fin 1).natAdd 237)
    | ⟨k+5,hk⟩ =>
      by_cases h : k+5<239
      · have hr := result (((⟨k,by omega⟩ : Fin 236).castAdd 1).castAdd 1)
        have hn : (⟨k+5,hk⟩ : Fin 242)≠239 := by intro he; have hv:=congrArg Fin.val he; change k+5=239 at hv; omega
        simpa only [slots,Fin.addCases_left,workSlot,show k<234 by omega,↓reduceIte,
          bankHeads,if_neg hn] using hr
      · have he : k+5=239 ∨ k+5=240 ∨ k+5=241 := by omega
        rcases he with he|he|he
        · have e : (⟨k+5,hk⟩ : Fin 242)=239 := Fin.ext he
          rw [e]
          exact kept 239 (by simp)
        · have e : (⟨k+5,hk⟩ : Fin 242)=240 := Fin.ext he
          rw [e]
          exact result (((235 : Fin 236).castAdd 1).castAdd 1)
        · have e : (⟨k+5,hk⟩ : Fin 242)=241 := Fin.ext he
          rw [e]
          exact kept 241 (by simp)
  exact ⟨r,hr,funext (fun i=>(all i).1),funext (fun i=>(all i).2),rs.trans_le bs.le⟩

end NearCubicWires.RepairSource.RecoveryTseitinTautology.Cold
