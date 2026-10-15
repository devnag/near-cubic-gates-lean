import Proof.CaseAnalysis.RowsSupportSymmetricCircuit
import Proof.CaseAnalysis.RowsCircuitPadding

/-! The same cold circuit runs in the already allocated term workspace.
Logical public streams stay unpadded; only private storage receives H cells. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Padding
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padding (P H : ℕ) : Fin 1704 → ℕ:=Fin.addCases (m:=1703) (n:=1)
  (CloseoutRowsCircuitPadding.padding P H) (fun _=>0)
def input (P H core W L : ℕ) (bits out supports : List Bool) : Fin 1704 → List Bool:=
  Fin.addCases (m:=1703) (n:=1) (CloseoutRowsCircuitPadding.input P H core W L bits out) (fun _=>supports)

theorem padded_input (P H core W L : ℕ) (bits out supports : List Bool) (i : Fin 1704) :
    ZeroPadding.pad (padding P H i) (Symmetric.input P core W L bits out supports i)=
      input P H core W L bits out supports i:=by
  refine Fin.addCases (m:=1703) (n:=1) ?_ ?_ i
  · intro j
    simp only [padding,Symmetric.input,input,Fin.addCases_left]
    exact CloseoutRowsCircuitPadding.padded_input P H core W L bits out j
  · intro j
    simp only [padding,Symmetric.input,input,Fin.addCases_right,ZeroPadding.pad_zero]

theorem run {s : ℕ} (p : Machine 1704 s) (P H core W L fuel : ℕ) (bits out next supports nextSupport : List Bool)
    (passed : Prop) (base : ExecutionReceipt 1704 s)
    (hr : runFrom p fuel ⟨p.start,Symmetric.heads out supports,
      Symmetric.input P core W L bits out supports⟩=some base)
    (hs : base.steps ≤ fuel) (flagHead : base.final.heads 1700=0)
    (flag : readTapeBit (base.final.tapes 1700) 0=true ↔ passed)
    (rawHead : base.final.heads 1=0) (raw : base.final.tapes 1=frame bits)
    (driverHead : base.final.heads 1694=0) (driver : base.final.tapes 1694=List.replicate P true)
    (good : passed →
      base.final.heads=Symmetric.heads (out++next) (supports++nextSupport) ∧
      base.final.tapes 1688=out++next ∧ base.final.tapes 1674=UnaryTemplate.tape core ∧
      base.final.tapes 1694=List.replicate P true ∧ base.final.tapes 1698=List.replicate W true ∧
      base.final.tapes 1699=List.replicate L true ∧ base.final.tapes 1=frame bits ∧
      base.final.tapes 1703=supports++nextSupport ∧
      ∀ i : Fin 1703,i≠1 → i≠1674 → i≠1694 → i≠1698 → i≠1699 → i≠1688 → (base.final.tapes (i.castAdd 1)).length ≤ P+1)
    (hH : P+1 ≤ H) : ∃ r,
    runFrom p fuel ⟨p.start,Symmetric.heads out supports,input P H core W L bits out supports⟩=some r ∧
    r.steps ≤ fuel ∧ r.final.heads 1700=0 ∧ (readTapeBit (r.final.tapes 1700) 0=true ↔ passed) ∧
    r.final.heads 1=0 ∧ r.final.tapes 1=ZeroPadding.pad P (frame bits) ∧
    r.final.heads 1694=0 ∧ r.final.tapes 1694=List.replicate P true ∧
    (passed →
      r.final.heads=Symmetric.heads (out++next) (supports++nextSupport) ∧
      r.final.tapes 1688=out++next ∧ r.final.tapes 1674=UnaryTemplate.tape core ∧
      r.final.tapes 1694=List.replicate P true ∧ r.final.tapes 1698=List.replicate W true ∧
      r.final.tapes 1699=List.replicate L true ∧ r.final.tapes 1=ZeroPadding.pad P (frame bits) ∧
      r.final.tapes 1703=supports++nextSupport ∧
      ∀ i : Fin 1703,i≠1 → i≠1674 → i≠1694 → i≠1698 → i≠1699 → i≠1688 → (r.final.tapes (i.castAdd 1)).length ≤ H) :=by
  obtain ⟨r,rr,rf,rs,_⟩:=ZeroPadding.run_config p (padding P H) fuel _ base hr
  have entry:ZeroPadding.config (padding P H)
      (⟨p.start,Symmetric.heads out supports,Symmetric.input P core W L bits out supports⟩ :
        Configuration 1704 s)=⟨p.start,Symmetric.heads out supports,input P H core W L bits out supports⟩:=
    configuration_ext rfl rfl (funext (padded_input P H core W L bits out supports))
  rw [entry] at rr
  have rh:r.final.heads=base.final.heads:=by rw [rf];rfl
  have rt (i : Fin 1704):r.final.tapes i=ZeroPadding.pad (padding P H i) (base.final.tapes i):=by rw [rf];rfl
  have raw':r.final.tapes 1=ZeroPadding.pad P (frame bits):=by rw [rt 1,raw];rfl
  have driver':r.final.tapes 1694=List.replicate P true:=by
    rw [rt 1694,driver];exact ZeroPadding.pad_zero _
  refine ⟨r,rr,rs ▸ hs,(congrFun rh 1700).trans flagHead,?_,(congrFun rh 1).trans rawHead,raw',
    (congrFun rh 1694).trans driverHead,driver',?_⟩
  · rw [rt 1700,ZeroPadding.read_pad];exact flag
  · intro hp
    obtain ⟨endHeads,native,domain,_c,w,l,_raw,supportTape,bounds⟩:=good hp
    refine ⟨rh.trans endHeads,?_,?_,driver',?_,?_,raw',?_,?_⟩
    · rw [rt 1688,native];exact ZeroPadding.pad_zero _
    · rw [rt 1674,domain];exact ZeroPadding.pad_zero _
    · rw [rt 1698,w];exact ZeroPadding.pad_zero _
    · rw [rt 1699,l];exact ZeroPadding.pad_zero _
    · rw [rt 1703,supportTape];exact ZeroPadding.pad_zero _
    · intro i h1 h2 h3 h4 h5 h6
      rw [rt (i.castAdd 1),ZeroPadding.pad_length,padding,Fin.addCases_left,
        CloseoutRowsCircuitPadding.private_padding P H i h1 h2 h3 h4 h5 h6]
      exact max_le le_rfl ((bounds i h1 h2 h3 h4 h5 h6).trans hH)

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Padding
