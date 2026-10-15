import Proof.CaseAnalysis.RecoveryCompile
import Proof.CaseAnalysis.RecoveryCompilePorts

/-! Insert the serializer's 1506 empty tapes between the unchanged graph
bank and the five retained raw scalars. This is an aliasing map, not a copy. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdGraph
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 158→Fin 1664:=Fin.addCases (m:=153) (n:=5)
  (fun j=>j.castAdd 1511) (fun j=>j.natAdd 1659)
def insert {α : Type} (empty : α) (A : Fin 158→α) : Fin 1664→α:=
  Fin.addCases (m:=1659) (n:=5)
    (Fin.addCases (m:=153) (n:=1506) (fun j=>A (j.castAdd 5)) (fun _=>empty))
    (fun j=>A (j.natAdd 153))

theorem injective : Function.Injective slots := by
  intro i j he
  revert he
  refine Fin.addCases (m:=153) (n:=5) (fun a=>?_) (fun a=>?_) i <;>
    refine Fin.addCases (m:=153) (n:=5) (fun b=>?_) (fun b=>?_) j
  all_goals
    intro he
    have hv:=congrArg Fin.val he
    simp only [slots,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at hv
    first
      | exact congrArg (fun k : Fin 153=>k.castAdd 5) (Fin.ext (by omega))
      | exact congrArg (fun k : Fin 5=>k.natAdd 153) (Fin.ext (by omega))
      | omega

theorem projection {α : Type} (empty : α) (A : Fin 158→α) (i : Fin 158) :
    insert empty A (slots i)=A i := by
  refine Fin.addCases (m:=153) (n:=5) (fun j=>?_) (fun j=>?_) i
  · have he : j.castAdd 1511=(j.castAdd 1506).castAdd 5 := rfl
    simp only [slots,Fin.addCases_left,he,insert,Fin.addCases_left]
  · simp only [slots,Fin.addCases_right,insert,Fin.addCases_right]

theorem other {α : Type} (empty : α) (A B : Fin 158→α) (i : Fin 1664)
    (hi : ∀ j,slots j≠i) : insert empty A i=insert empty B i := by
  revert hi
  refine Fin.addCases (m:=1659) (n:=5) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=153) (n:=1506) (fun k=>?_) (fun k=>?_) j
    · intro h
      exact False.elim (h (k.castAdd 5) (by simp only [slots,Fin.addCases_left];rfl))
    · intro _
      simp only [insert,Fin.addCases_left,Fin.addCases_right]
  · intro h
    exact False.elim (h (j.natAdd 153) (by simp only [slots,Fin.addCases_right]))

theorem constant {α : Type} (a : α) : insert a (fun _=>a)=fun _=>a := by
  funext i
  refine Fin.addCases (m:=1659) (n:=5) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=153) (n:=1506) (fun k=>?_) (fun k=>?_) j <;>
      simp only [insert,Fin.addCases_left,Fin.addCases_right]
  · simp only [insert,Fin.addCases_right]

theorem run_insert {s : ℕ} (worker : Machine 158 s) (fuel : ℕ) (A : Fin 158→List Bool)
    (r : ExecutionReceipt 158 s) (hr : run worker fuel A=some r) :
    ∃ result,run (RecoveryFocus.machine slots worker) fuel (insert [] A)=some result ∧
      result.steps=r.steps ∧ result.final.heads=insert 0 r.final.heads ∧
      result.final.tapes=insert [] r.final.tapes := by
  obtain ⟨result,rr,_,rs,rh,rt,keep⟩:=RecoveryFocus.dock slots injective worker fuel
    (fun _=>0) (insert [] A) (initialConfiguration worker A)
    (by intro j;rfl) (projection [] A) r hr
  refine ⟨result,rr,rs,?_,?_⟩
  · funext i
    by_cases hs : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hs
      exact (rh j).trans (projection 0 r.final.heads j).symm
    · have hn : ∀ j,slots j≠i:=by simpa only [not_exists] using hs
      rw [(keep i hn).1]
      have h:=other 0 (fun _=>0) r.final.heads i hn
      rw [constant] at h
      exact h
  · funext i
    by_cases hs : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hs
      exact (rt j).trans (projection [] r.final.tapes j).symm
    · have hn : ∀ j,slots j≠i:=by simpa only [not_exists] using hs
      exact (keep i hn).2.trans (other [] A r.final.tapes i hn)

end NearCubicWires.RepairOrdinary.RecoveryBoundedColdGraph
