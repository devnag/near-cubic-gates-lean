import Proof.CaseAnalysis.RowsCircuitAliases

/-! The same cold circuit runs in the already allocated term workspace.
Logical public streams stay unpadded; only private storage receives H cells. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitPadding
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padding (P H : ℕ) (i : Fin 1703):=
  if i=1 then P else if i=1674 ∨ i=1688 ∨ i=1694 ∨ i=1698 ∨ i=1699 then 0 else H
def input (P H core W L : ℕ) (bits out : List Bool) (i : Fin 1703):=
  if i=1 then ZeroPadding.pad P (frame bits) else if i=1674 then UnaryTemplate.tape core
  else if i=1688 then out else if i=1694 then List.replicate P true
  else if i=1698 then List.replicate W true else if i=1699 then List.replicate L true
  else List.replicate H false

theorem padded_input (P H core W L : ℕ) (bits out : List Bool) (i : Fin 1703) :
    ZeroPadding.pad (padding P H i) (CloseoutRowsCircuitColdEntry.input P core W L bits out i)=
      input P H core W L bits out i:=by
  have eqval (a : Fin 1703) : i=a ↔ i.val=a.val:=Fin.ext_iff
  simp only [padding,input,CloseoutRowsCircuitColdEntry.input,CloseoutRowsCircuit.input,eqval]
  split_ifs <;> simp_all [ZeroPadding.pad]

theorem private_padding (P H : ℕ) (i : Fin 1703)
    (h1 : i≠1) (h2 : i≠1674) (h3 : i≠1694) (h4 : i≠1698) (h5 : i≠1699) (h6 : i≠1688) :
    padding P H i=H:=by simp only [padding,h1,h2,h3,h4,h5,h6,or_self,ite_false]

theorem run {s : ℕ} (p : Machine 1703 s) (P H core W L fuel : ℕ) (bits out next : List Bool)
    (passed : Prop) (base : ExecutionReceipt 1703 s)
    (hr : runFrom p fuel ⟨p.start,CloseoutRowsCircuitColdEntry.heads out,
      CloseoutRowsCircuitColdEntry.input P core W L bits out⟩=some base)
    (hs : base.steps ≤ fuel) (flagHead : base.final.heads 1700=0)
    (flag : readTapeBit (base.final.tapes 1700) 0=true ↔ passed)
    (rawHead : base.final.heads 1=0) (raw : base.final.tapes 1=frame bits)
    (driverHead : base.final.heads 1694=0) (driver : base.final.tapes 1694=List.replicate P true)
    (good : passed →
      base.final.heads=CloseoutRowsCircuitColdEntry.heads (out++next) ∧
      base.final.tapes 1688=out++next ∧ base.final.tapes 1674=UnaryTemplate.tape core ∧
      base.final.tapes 1694=List.replicate P true ∧ base.final.tapes 1698=List.replicate W true ∧
      base.final.tapes 1699=List.replicate L true ∧ base.final.tapes 1=frame bits ∧
      ∀ i,i≠1 → i≠1674 → i≠1694 → i≠1698 → i≠1699 → i≠1688 → (base.final.tapes i).length ≤ P+1)
    (hH : P+1 ≤ H) : ∃ r,
    runFrom p fuel ⟨p.start,CloseoutRowsCircuitColdEntry.heads out,input P H core W L bits out⟩=some r ∧
    r.steps ≤ fuel ∧ r.final.heads 1700=0 ∧ (readTapeBit (r.final.tapes 1700) 0=true ↔ passed) ∧
    r.final.heads 1=0 ∧ r.final.tapes 1=ZeroPadding.pad P (frame bits) ∧
    r.final.heads 1694=0 ∧ r.final.tapes 1694=List.replicate P true ∧
    (passed →
      r.final.heads=CloseoutRowsCircuitColdEntry.heads (out++next) ∧
      r.final.tapes 1688=out++next ∧ r.final.tapes 1674=UnaryTemplate.tape core ∧
      r.final.tapes 1694=List.replicate P true ∧ r.final.tapes 1698=List.replicate W true ∧
      r.final.tapes 1699=List.replicate L true ∧ r.final.tapes 1=ZeroPadding.pad P (frame bits) ∧
      ∀ i,i≠1 → i≠1674 → i≠1694 → i≠1698 → i≠1699 → i≠1688 → (r.final.tapes i).length ≤ H):=by
  obtain ⟨r,rr,rf,rs,_⟩:=ZeroPadding.run_config p (padding P H) fuel _ base hr
  have entry:ZeroPadding.config (padding P H)
      (⟨p.start,CloseoutRowsCircuitColdEntry.heads out,CloseoutRowsCircuitColdEntry.input P core W L bits out⟩ :
        Configuration 1703 s)=⟨p.start,CloseoutRowsCircuitColdEntry.heads out,input P H core W L bits out⟩:=
    configuration_ext rfl rfl (funext (padded_input P H core W L bits out))
  rw [entry] at rr
  have rh:r.final.heads=base.final.heads:=by rw [rf];rfl
  have rt (i : Fin 1703):r.final.tapes i=ZeroPadding.pad (padding P H i) (base.final.tapes i):=by rw [rf];rfl
  have raw':r.final.tapes 1=ZeroPadding.pad P (frame bits):=by rw [rt 1,raw];rfl
  have driver':r.final.tapes 1694=List.replicate P true:=by
    rw [rt 1694,driver];exact ZeroPadding.pad_zero _
  refine ⟨r,rr,rs ▸ hs,(congrFun rh 1700).trans flagHead,?_,(congrFun rh 1).trans rawHead,raw',
    (congrFun rh 1694).trans driverHead,driver',?_⟩
  · rw [rt 1700,ZeroPadding.read_pad];exact flag
  · intro hp
    obtain ⟨heads,native,domain,_c,w,l,_raw,support⟩:=good hp
    refine ⟨rh.trans heads,?_,?_,driver',?_,?_,raw',?_⟩
    · rw [rt 1688,native];exact ZeroPadding.pad_zero _
    · rw [rt 1674,domain];exact ZeroPadding.pad_zero _
    · rw [rt 1698,w];exact ZeroPadding.pad_zero _
    · rw [rt 1699,l];exact ZeroPadding.pad_zero _
    · intro i h1 h2 h3 h4 h5 h6
      rw [rt i,ZeroPadding.pad_length,private_padding P H i h1 h2 h3 h4 h5 h6]
      exact max_le le_rfl ((support i h1 h2 h3 h4 h5 h6).trans hH)

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitPadding
