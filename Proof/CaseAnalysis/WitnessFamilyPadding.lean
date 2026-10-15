import Proof.CaseAnalysis.WitnessFamilyLoopRun

/-! The outer count driver reuses its existing zero allocation. The same
literal rejecting repeater has the same steps and logical result; no
sum or retained record stream receives new padding or a second copy. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.CountedFamily
open LocalBitMultitape
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def pads {t : ℕ} (H : ℕ) (i : Fin (t+1)):=if i.val=t then H else 0

theorem padded_data {t : ℕ} (H : ℕ) (left : Fin t → List Bool) (right : List Bool) :
    (fun i=>ZeroPadding.pad (pads H i)
      (Fin.addCases (m:=t) (n:=1) (motive:=fun _=>List Bool) left (fun _=>right) i))=
    Fin.addCases (m:=t) (n:=1) (motive:=fun _=>List Bool) left (fun _=>ZeroPadding.pad H right) := by
  funext i
  refine Fin.addCases (m:=t) (n:=1) ?_ ?_ i
  · intro j
    simp only [Fin.addCases_left,pads,Fin.val_castAdd,if_neg (Nat.ne_of_lt j.isLt),ZeroPadding.pad_zero]
  · intro j
    have hj:j=0:=Fin.eq_zero j
    subst j
    simp only [Fin.addCases_right]
    change ZeroPadding.pad (if t+0=t then H else 0) right=ZeroPadding.pad H right
    simp only [Nat.add_zero,ite_true]

def PaddedRun {α : Type} {t s : ℕ} (body : Machine t s) (source : ℕ → α → Configuration t s)
    (Inv : ℕ → α → Prop) (H cost total : ℕ) (bit : Fin t) (initial : α) (flag : Bool) : Prop :=
  ∃ r,runFrom (RepeatMachine.machine body (fun _ bits=>bits bit)) (total*(cost+3)+3)
    (ZeroPadding.config (pads H) (RepeatMachine.cfg 0 (source 0 initial) total 1))=some r ∧
    r.steps ≤ total*(cost+3)+3 ∧ r.final.heads (bit.castAdd 1)=0 ∧ r.final.tapes (bit.castAdd 1)=[flag] ∧
    (flag=true → ∃ after,
      r.final=ZeroPadding.config (pads H) (RepeatMachine.cfg 3 (source total after) total 1) ∧ Inv total after)

theorem padded_run {α : Type} {t s : ℕ} (body : Machine t s) (source : ℕ → α → Configuration t s)
    (Inv : ℕ → α → Prop) (H cost total : ℕ) (bit : Fin t) (initial : α) (flag : Bool)
    (h : Run body source Inv cost total bit initial flag) :
    PaddedRun body source Inv H cost total bit initial flag := by
  obtain ⟨base,hbase,bs,bh,bt,good⟩:=h
  obtain ⟨r,run,rf,rs,_⟩:=ZeroPadding.run_config (RepeatMachine.machine body (fun _ bits=>bits bit))
    (pads H) _ _ base hbase
  refine ⟨r,run,rs.trans_le bs,?_,?_,?_⟩
  · rw [rf];exact bh
  · rw [rf]
    change ZeroPadding.pad (pads H (bit.castAdd 1)) (base.final.tapes (bit.castAdd 1))=[flag]
    simp only [pads,Fin.val_castAdd,if_neg (Nat.ne_of_lt bit.isLt),ZeroPadding.pad_zero,bt]
  · intro accepted
    obtain ⟨after,ah,inv⟩:=good accepted
    exact ⟨after,rf.trans (congrArg (ZeroPadding.config (pads H)) ah),inv⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.CountedFamily
