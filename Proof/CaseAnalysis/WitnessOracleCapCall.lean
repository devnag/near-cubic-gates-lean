import Proof.CaseAnalysis.WitnessOracleCap

/-! The exact cap checker aliases the two actual metadata counters. Every
old tape and head is retained, so the original native continuation reuses them. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.OracleCap.Call
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev extra (G : ℕ):=Core.tapes (degree G)
def old (G : ℕ) {t : ℕ} (i : Fin t) : Fin (t+extra G):=i.castAdd (extra G)
def slots (G : ℕ) {t : ℕ} (fields : Fin 2→Fin t) (i : Fin (extra G)) : Fin (t+extra G):=
  if i.val=0 then old G (fields 0) else if i.val=1 then old G (fields 1) else i.natAdd t

theorem slots_injective (G : ℕ) {t : ℕ} (fields : Fin 2→Fin t) (hf : Function.Injective fields) :
    Function.Injective (slots G fields):=by
  have h01:(fields 0).val≠(fields 1).val:=fun h=>(by decide : (0 : Fin 2)≠1) (hf (Fin.ext h))
  have h0:=(fields 0).isLt
  have h1:=(fields 1).isLt
  intro a b he
  have hv:=congrArg Fin.val he
  dsimp only [slots,old] at hv
  split_ifs at hv <;> dsimp at hv <;> apply Fin.ext <;> omega

def input (G : ℕ) {t : ℕ} (base : Fin t→List Bool) : Fin (t+extra G)→List Bool:=
  Fin.addCases base (fun _=>[])
def heads (G : ℕ) {t : ℕ} (base : Fin t→ℕ) : Fin (t+extra G)→ℕ:=
  Fin.addCases base (fun _=>0)
def machine (G : ℕ) {t : ℕ} (fields : Fin 2→Fin t):=
  RecoveryFocus.machine (slots G fields) (OracleCap.machine G)
def flagSlot (G : ℕ) {t : ℕ} (fields : Fin 2→Fin t):=
  slots G fields (Core.flagSlot (degree G))

theorem input_old (G : ℕ) {t : ℕ} (base : Fin t→List Bool) (i : Fin t) :
    input G base (old G i)=base i:=by simp only [input,old,Fin.addCases_left]
theorem heads_old (G : ℕ) {t : ℕ} (base : Fin t→ℕ) (i : Fin t) :
    heads G base (old G i)=base i:=by simp only [heads,old,Fin.addCases_left]

theorem outside (G : ℕ) {t : ℕ} (fields : Fin 2→Fin t) (i : Fin t)
    (h0:i≠fields 0) (h1:i≠fields 1) : ∀ j,slots G fields j≠old G i:=by
  have h0':i.val≠(fields 0).val:=fun h=>h0 (Fin.ext h)
  have h1':i.val≠(fields 1).val:=fun h=>h1 (Fin.ext h)
  intro j hj
  have hv:=congrArg Fin.val hj
  dsimp only [slots,old] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

theorem call_run (G : ℕ) {t : ℕ} (fields : Fin 2→Fin t) (hf : Function.Injective fields)
    (base : Fin t→List Bool) (cursor : Fin t→ℕ) (q size : ℕ)
    (hh : ∀ j,cursor (fields j)=0)
    (hq : base (fields 0)=List.replicate q true)
    (hs : base (fields 1)=List.replicate size true) :
    ∃ actual,runFrom (machine G fields) (OracleCap.budget G q size)
      ⟨(machine G fields).start,heads G cursor,input G base⟩=some actual ∧
      actual.steps  ≤  OracleCap.budget G q size ∧
      (∀ i,actual.final.heads (old G i)=cursor i ∧ actual.final.tapes (old G i)=base i) ∧
      actual.final.heads (flagSlot G fields)=0 ∧
      actual.final.tapes (flagSlot G fields)=[decide (size  ≤  RecoveryScheduleEnvelope.oracleSizeBound G q)]:=by
  obtain ⟨out,⟨r,hr,rt,rh,rs⟩,rq,rsize,rf⟩:=OracleCap.cap_run G q size
  have hheads (j : Fin (extra G)) : heads G cursor (slots G fields j)=0:=by
    dsimp only [slots]
    split_ifs
    · exact (heads_old G cursor _).trans (hh 0)
    · exact (heads_old G cursor _).trans (hh 1)
    · simp only [heads,Fin.addCases_right]
  have hdata (j : Fin (extra G)) : input G base (slots G fields j)=Core.input (degree G) q size j:=by
    dsimp only [slots,Core.input]
    split_ifs
    · exact (input_old G base _).trans hq
    · exact (input_old G base _).trans hs
    · simp only [input,Fin.addCases_right]
  obtain ⟨a,ha,_,asteps,ah,atape,away⟩:=RecoveryFocus.dock (slots G fields) (slots_injective G fields hf)
    (OracleCap.machine G) (OracleCap.budget G q size) (heads G cursor) (input G base)
    (initialConfiguration (OracleCap.machine G) (Core.input (degree G) q size)) hheads hdata r hr
  refine ⟨a,ha,asteps.trans_le rs,?_,(ah _).trans (rh _),(atape _).trans ((congrFun rt _).trans rf)⟩
  intro i
  by_cases h0:i=fields 0
  · subst i
    have he:old G (fields 0)=slots G fields (Core.qSlot (degree G)):=rfl
    rw [he,ah,atape,rt,rh,rq]
    exact ⟨(hh 0).symm,hq.symm⟩
  by_cases h1:i=fields 1
  · subst i
    have he:old G (fields 1)=slots G fields (Core.sizeSlot (degree G)):=rfl
    rw [he,ah,atape,rt,rh,rsize]
    exact ⟨(hh 1).symm,hs.symm⟩
  obtain ⟨hk,tk⟩:=away (old G i) (outside G fields i h0 h1)
  exact ⟨hk.trans (heads_old G cursor i),tk.trans (input_old G base i)⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.OracleCap.Call
