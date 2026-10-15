import Proof.CaseAnalysis.RowsTupleSeekTupleRun

/-! The enclosing tuple call starts at the family producer's actual end
cursors and pays their reset before executing the requested indices. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape ExtDecompositionBatch RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tupleHeads (pos : Fin 3 → ℕ) (out : Fin 4 → List Bool) (ip : ℕ) : Fin 27 → ℕ :=
  Fin.addCases (m:=26) (n:=1) (motive:=fun _=>ℕ) (RawLoop.heads (familyHeads pos out) ip) (fun _=>1)
def tupleData (C D : ℕ) (src : Fin 3 → List Bool) (out : Fin 4 → List Bool) (index : List Bool) (Q : ℕ) : Fin 27 → List Bool :=
  Fin.addCases (m:=26) (n:=1) (motive:=fun _=>List Bool) (RawLoop.data (familyData C D src out) index)
    (fun _=>CompareMachine.word Q)
noncomputable def coldMachine := Composition.machine (TapeEmbedding.machine 2 familyRewind) tupleMachine

theorem two_extras {α : Type} (A : Fin 25 → α) (a b : α) :
    (Fin.addCases (m:=25) (n:=2) (motive:=fun _=>α) A ![a,b])=
      Fin.addCases (m:=26) (n:=1) (motive:=fun _=>α)
        (Fin.addCases (m:=25) (n:=1) (motive:=fun _=>α) A (fun _=>a)) (fun _=>b) := by
  funext i;fin_cases i <;> rfl

theorem step_of_counted {t s fuel : ℕ} (p : Machine t s) (a b : Configuration t s) (Q : ℕ)
    (r : ExecutionReceipt (t+1) (Fintype.card (RepeatMachine.Control s)))
    (hr : runFrom (RepeatMachine.machine p (fun _ _=>true)) fuel (RepeatMachine.cfg 0 a Q 1)=some r)
    (hf : r.final=RepeatMachine.cfg 3 b Q 1) (hs : r.steps ≤ fuel) :
    Step (RepeatMachine.machine p (fun _ _=>true)) fuel
      (Fin.addCases a.heads (fun _ : Fin 1=>1)) (Fin.addCases a.tapes (fun _ : Fin 1=>CompareMachine.word Q))
      (Fin.addCases b.heads (fun _ : Fin 1=>1)) (Fin.addCases b.tapes (fun _ : Fin 1=>CompareMachine.word Q)) :=
  ⟨r,hr,by rw [hf];rfl,by rw [hf];rfl,hs⟩

theorem cold_run (ts : List TermSlices) (js : List (Fin ts.length)) (C D : ℕ)
    (hC : ∀ t∈ts,t.cost+1 ≤ C) (hD : ∀ i,(familyWords ts i).length ≤ D)
    (pre tail : List Bool) (out : Fin 4 → List Bool) (hfour : js.length ≤ 4)
    (pos : Fin 3 → ℕ) (hp : ∀ i,pos i ≤ D) :
    Step coldMachine (6*D+9+tupleBudget C D ts.length 4)
      (tupleHeads pos out pre.length) (tupleData C D (familyWords ts) out (pre++tupleWord js++tail) js.length)
      (tupleHeads (fun _=>0) (tupleOutput ts js out) (pre.length+(tupleWord js).length))
      (tupleData C D (familyWords ts) (tupleOutput ts js out) (pre++tupleWord js++tail) js.length) := by
  obtain ⟨r,hr,rf,rs⟩ := tuple_run ts js C D hC hD pre tail out hfour
  have last := step_of_counted indexedMachine _ _ js.length r hr rf rs
  have first := (family_rewind_run C D (familyWords ts) pos out hp).embed
    ![pre.length,1] ![pre++tupleWord js++tail,CompareMachine.word js.length]
  simp only [two_extras] at first
  have all := first.seq last
  have time : 6*D+8+1+tupleBudget C D ts.length 4=6*D+9+tupleBudget C D ts.length 4 := by omega
  rw [time] at all
  exact all

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
