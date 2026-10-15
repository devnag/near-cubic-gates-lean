import Proof.CaseAnalysis.WitnessSourcePolicy

/-! Alias the public source and head-one cache domain into the one-time
policy. Every old tape and cursor is retained, including the reusable cache. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.Call
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev extra (D : ℕ):=SourcePolicy.tapes D
def old (D : ℕ) {t : ℕ} (i : Fin t) : Fin (t+extra D):=i.castAdd (extra D)
def slots (D : ℕ) {t : ℕ} (fields : Fin 2→Fin t) (i : Fin (extra D)) : Fin (t+extra D):=
  if i.val=0 then old D (fields 0) else if i.val=42 then old D (fields 1) else i.natAdd t
def input (D : ℕ) {t : ℕ} (base : Fin t→List Bool) : Fin (t+extra D)→List Bool:=
  Fin.addCases base (fun _=>[])
def heads (D : ℕ) {t : ℕ} (base : Fin t→ℕ) : Fin (t+extra D)→ℕ:=
  Fin.addCases base (fun _=>0)
def machine (D copies : ℕ) (delta : ℚ) {t : ℕ} (fields : Fin 2→Fin t):=
  RecoveryFocus.machine (slots D fields) (SourcePolicy.machine D copies delta)

theorem slots_injective (D : ℕ) {t : ℕ} (fields : Fin 2→Fin t) (hf : Function.Injective fields) :
    Function.Injective (slots D fields):=by
  have h01:(fields 0).val≠(fields 1).val:=fun h=>(by decide : (0 : Fin 2)≠1) (hf (Fin.ext h))
  have h0:=(fields 0).isLt
  have h1:=(fields 1).isLt
  intro a b he
  have hv:=congrArg (fun i : Fin (t+extra D)=>i.val) he
  dsimp only [slots,old] at hv
  split_ifs at hv <;> dsimp at hv <;> apply Fin.ext <;> omega
theorem input_old (D : ℕ) {t : ℕ} (base : Fin t→List Bool) (i : Fin t) :
    input D base (old D i)=base i:=by simp only [input,old,Fin.addCases_left]
theorem heads_old (D : ℕ) {t : ℕ} (base : Fin t→ℕ) (i : Fin t) :
    heads D base (old D i)=base i:=by simp only [heads,old,Fin.addCases_left]
theorem outside (D : ℕ) {t : ℕ} (fields : Fin 2→Fin t) (i : Fin t)
    (h0:i≠fields 0) (h1:i≠fields 1) : ∀ j,slots D fields j≠old D i:=by
  have h0':i.val≠(fields 0).val:=fun h=>h0 (Fin.ext h)
  have h1':i.val≠(fields 1).val:=fun h=>h1 (Fin.ext h)
  intro j hj
  have hv:=congrArg (fun i : Fin (t+extra D)=>i.val) hj
  dsimp only [slots,old] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

structure Fields (D copies : ℕ) (delta : ℚ) {t n0 s : ℕ} (fields : Fin 2→Fin t)
    (r : PCPPRequest n0) (p : PointwisePCPP r.circuit)
    (cfg : Configuration (t+extra D) s) : Prop where
  count : cfg.tapes (slots D fields (SourcePolicy.countSlots D 40))=
    List.replicate (p.systematicBits+p.auxiliaryBits) true
  clause : cfg.tapes (slots D fields (SourcePolicy.countSlots D 38))=List.replicate p.clauseBits true
  q0 : cfg.tapes (slots D fields (SourcePolicy.q0Slot D))=List.replicate (CorePolicy.q0 D r.arity) true
  cap : cfg.tapes (slots D fields (SourcePolicy.capSlot D))=List.replicate
    (natBitLength (CloseoutXor.cap delta (CorePolicy.q0 D r.arity) copies*max 1 (2*2^p.clauseBits))) true
  cursor : ∀ i,cfg.heads (slots D fields i)=SourcePolicy.heads D i

theorem call_run (D copies : ℕ) (delta : ℚ) {t n0 : ℕ}
    (fields : Fin 2→Fin t) (hf : Function.Injective fields)
    (base : Fin t→List Bool) (cursor : Fin t→ℕ) (r : PCPPRequest n0) (p : PointwisePCPP r.circuit)
    (hD : 1 ≤ D) (hh0 : cursor (fields 0)=0) (hh1 : cursor (fields 1)=1)
    (hs : base (fields 0)=pcppOutput r p) (hd : base (fields 1)=UnaryTemplate.tape r.arity) :
    ∃ actual,runFrom (machine D copies delta fields)
      (SourcePolicy.budget D copies r.arity p.systematicBits p.auxiliaryBits p.clauseBits delta)
      ⟨(machine D copies delta fields).start,heads D cursor,input D base⟩=some actual ∧
      actual.steps ≤ SourcePolicy.budget D copies r.arity p.systematicBits p.auxiliaryBits p.clauseBits delta ∧
      (∀ i,actual.final.heads (old D i)=cursor i ∧ actual.final.tapes (old D i)=base i) ∧
      Fields D copies delta fields r p actual.final:=by
  obtain ⟨r0,hr,rs,rh,rt,rV,rc,rdom,rq,rb⟩:=SourcePolicy.actual_run r p D copies delta hD
  have hheads (j : Fin (extra D)) : heads D cursor (slots D fields j)=SourcePolicy.heads D j:=by
    by_cases h0:j.val=0
    · rw [slots,if_pos h0,heads_old,hh0]
      simp only [SourcePolicy.heads,h0,show ¬(0 : ℕ)=42 by decide,if_false]
    by_cases h42:j.val=42
    · rw [slots,if_neg h0,if_pos h42,heads_old,hh1]
      simp only [SourcePolicy.heads,if_pos h42]
    rw [slots,if_neg h0,if_neg h42]
    simp only [heads,Fin.addCases_right,SourcePolicy.heads,if_neg h42]
  have hdata (j : Fin (extra D)) : input D base (slots D fields j)=SourcePolicy.input D r.arity (pcppOutput r p) j:=by
    by_cases h0:j.val=0
    · rw [slots,if_pos h0,input_old,hs]
      simp only [SourcePolicy.input,if_pos h0]
    by_cases h42:j.val=42
    · rw [slots,if_neg h0,if_pos h42,input_old,hd]
      simp only [SourcePolicy.input,if_neg h0,if_pos h42]
    rw [slots,if_neg h0,if_neg h42]
    simp only [input,Fin.addCases_right,SourcePolicy.input,if_neg h0,if_neg h42]
  obtain ⟨a,ha,_,asteps,ah,atape,away⟩:=RecoveryFocus.dock (slots D fields) (slots_injective D fields hf)
    (SourcePolicy.machine D copies delta) _ (heads D cursor) (input D base)
    (SourcePolicy.entry D copies r.arity delta (pcppOutput r p)) hheads hdata r0 hr
  refine ⟨a,ha,asteps.trans_le rs,?_,⟨(atape _).trans rV,(atape _).trans rc,
    (atape _).trans rq,(atape _).trans rb,fun i=>(ah i).trans (congrFun rh i)⟩⟩
  intro i
  by_cases h0:i=fields 0
  · subst i
    have he:old D (fields 0)=slots D fields (SourcePolicy.countSlots D 0):=rfl
    rw [he,ah,atape,rh,rt]
    exact ⟨hh0.symm,hs.symm⟩
  by_cases h1:i=fields 1
  · subst i
    have he:old D (fields 1)=slots D fields (SourcePolicy.coreSlot D):=rfl
    rw [he,ah,atape,rh,rdom]
    exact ⟨hh1.symm,hd.symm⟩
  obtain ⟨hk,tk⟩:=away (old D i) (outside D fields i h0 h1)
  exact ⟨hk.trans (heads_old D cursor i),tk.trans (input_old D base i)⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.Call
