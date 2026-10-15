import Proof.CaseAnalysis.RecoveryGraphLayout
import Proof.CaseAnalysis.RecoveryGraphSerializeRun

/-! Compose the unchanged graph compiler and cold serializer at symbolic
state counts. The actual five scalar words stay outside the serializer. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdGraph
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem insert_append {α : Type} (empty : α) (A : Fin 153→α) (E : Fin 5→α) :
    insert empty (Fin.addCases (m:=153) (n:=5) A E)=
      Fin.addCases (m:=1659) (n:=5)
        (Fin.addCases (m:=153) (n:=1506) A (fun _=>empty)) E := by
  funext i
  refine Fin.addCases (m:=1659) (n:=5) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=153) (n:=1506) (fun k=>?_) (fun k=>?_) j <;>
      simp only [insert,Fin.addCases_left,Fin.addCases_right]
  · simp only [insert,Fin.addCases_right]

namespace Join
noncomputable def machine {s t : ℕ} (first : Machine 158 s) (last : Machine 1659 t):=
  Composition.machine (RecoveryFocus.machine slots first) (TapeEmbedding.machine 5 last)

theorem run {s t : ℕ} {ι : Type} (first : Machine 158 s) (last : Machine 1659 t)
    (u v : ℕ) (A : Fin 158→List Bool) (E : Fin 5→List Bool)
    (H : ι→Fin 153→ℕ) (T : ι→Fin 153→List Bool) (payload arity : List Bool)
    (hp : ∃ i,∃ p,LocalBitMultitape.run first u A=some p ∧ p.steps≤u ∧
      p.final.heads=Fin.addCases (m:=153) (n:=5) (H i) (fun _=>0) ∧
      p.final.tapes=Fin.addCases (m:=153) (n:=5) (T i) E)
    (hq : ∀ i,∃ q,runFrom last v
      ⟨last.start,Fin.addCases (m:=153) (n:=1506) (H i) (fun _=>0),
        Fin.addCases (m:=153) (n:=1506) (T i) (fun _=>[])⟩=some q ∧
      q.final.tapes 1657=payload ∧ q.final.heads 1657=0 ∧ q.steps≤v ∧
      q.final.tapes 144=arity ∧ q.final.heads 144=0) :
    ∃ r,LocalBitMultitape.run (machine first last) (u+1+v) (insert [] A)=some r ∧
      r.steps≤u+1+v ∧ r.final.tapes 1657=payload ∧ r.final.heads 1657=0 ∧
      r.final.tapes 144=arity ∧ r.final.heads 144=0 ∧
      (∀ j : Fin 5,r.final.tapes (j.natAdd 1659)=E j ∧ r.final.heads (j.natAdd 1659)=0) := by
  obtain ⟨i,p,pr,ps,ph,pt⟩:=hp
  obtain ⟨a,ar,as,ah,atapes⟩:=run_insert first u A p pr
  rw [ph,insert_append] at ah
  rw [pt,insert_append] at atapes
  obtain ⟨q,qr,qo,qh,qs,qa,qah⟩:=hq i
  let b:=TapeEmbedding.receipt (fun _ : Fin 5=>0) E q
  have br:=TapeEmbedding.run_embed last (fun _ : Fin 5=>0) E v _ q qr
  have br' : runFrom (TapeEmbedding.machine 5 last) v
      (Composition.restart a.final (TapeEmbedding.machine 5 last).start)=some b := by
    change runFrom _ _ ⟨_,a.final.heads,a.final.tapes⟩=some b
    rw [ah,atapes]
    exact br
  refine ⟨Composition.joinedReceipt a b,
    Composition.run_join (RecoveryFocus.machine slots first) (TapeEmbedding.machine 5 last) _ _ _ a b ar br',
    Nat.add_le_add (Nat.add_le_add_right (as.trans_le ps) 1) qs,?_,?_,?_,?_,?_⟩
  · exact (TapeEmbedding.receipt_tapes_old (fun _ : Fin 5=>0) E q 1657).trans qo
  · exact (TapeEmbedding.receipt_heads_old (fun _ : Fin 5=>0) E q 1657).trans qh
  · exact (TapeEmbedding.receipt_tapes_old (fun _ : Fin 5=>0) E q 144).trans qa
  · exact (TapeEmbedding.receipt_heads_old (fun _ : Fin 5=>0) E q 144).trans qah
  · intro j
    exact ⟨TapeEmbedding.receipt_tapes_new (fun _ : Fin 5=>0) E q j,
      TapeEmbedding.receipt_heads_new (fun _ : Fin 5=>0) E q j⟩
end Join

end NearCubicWires.RepairOrdinary.RecoveryBoundedColdGraph
