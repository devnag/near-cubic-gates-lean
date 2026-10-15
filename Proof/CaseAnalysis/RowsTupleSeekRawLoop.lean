import Proof.CaseAnalysis.RowsTupleSeekRewind

/-! The caller's original-term unary block drives an actual ordinary loop.
There is no integer decoder and no reordering of requested indices. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek.RawLoop
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads {t : ℕ} (H : Fin t → ℕ) (ip : ℕ) : Fin (t+1) → ℕ :=
  Fin.addCases (m:=t) (n:=1) (motive:=fun _=>ℕ) H (fun _=>ip)
def data {t : ℕ} (A : Fin t → List Bool) (index : List Bool) : Fin (t+1) → List Bool :=
  Fin.addCases (m:=t) (n:=1) (motive:=fun _=>List Bool) A (fun _=>index)
def advance (t : ℕ) : Machine (t+1) 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,fun _=>none,
    Fin.addCases (fun _ : Fin t=>.stay) (fun _ : Fin 1=>.right)⟩ else none
noncomputable def body {t s : ℕ} (p : Machine t s) := Composition.machine (TapeEmbedding.machine 1 p) (advance t)
def idle (t : ℕ) : Machine (t+1) 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
def sizes (s : ℕ) : Fin 2 → ℕ := ![1,s+2]
noncomputable def programs {t s : ℕ} (p : Machine t s) : (i : Fin 2) → Machine (t+1) (sizes s i)
  | ⟨0,_⟩=>idle t
  | ⟨1,_⟩=>body p
  | ⟨n+2,h⟩=>False.elim (by omega)
def next {t s : ℕ} (i : Fin 2) (_ : Fin (sizes s i)) (bits : Fin (t+1) → Bool) : Option (Fin 2) :=
  if i=0 then if bits (Fin.last t) then some 1 else none else some 0
noncomputable def loop {t s : ℕ} (p : Machine t s) := RecoveryCalls.machine (sizes s) (programs p) 0 next
noncomputable def entry {t s : ℕ} (p : Machine t s) (i : Fin 2) (H : Fin t → ℕ)
    (A : Fin t → List Bool) (ip : ℕ) (index : List Bool) :=
  controlConfig (RecoveryCalls.code (sizes s) i)
    (⟨(programs p i).start,heads H ip,data A index⟩ : Configuration (t+1) (sizes s i))
noncomputable def final {t s : ℕ} (H : Fin t → ℕ) (A : Fin t → List Bool) (ip : ℕ) (index : List Bool) :=
  RecoveryCalls.stopped (sizes s) (heads H ip) (data A index)
noncomputable def machine {t s : ℕ} (p : Machine t s) := Composition.machine
  (Composition.machine (advance t) (loop p)) (advance t)

theorem advance_run {t : ℕ} (H : Fin t → ℕ) (A : Fin t → List Bool) (ip : ℕ) (index : List Bool) :
    Step (advance t) 1 (heads H ip) (data A index) (heads H (ip+1)) (data A index) := by
  have hs : step (advance t) ⟨0,heads H ip,data A index⟩=some ⟨1,heads H (ip+1),data A index⟩ := by
    simp only [step,advance,↓reduceIte,Option.map_some]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=t) (n:=1) (fun j=>?_) (fun j=>?_) i
      · simp [applyAction,HeadMove.apply,heads,Fin.addCases_left]
      · simp [applyAction,HeadMove.apply,heads,Fin.addCases_right]
    · rfl
  obtain ⟨r,hr,rf,_⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

theorem body_run {t s cost : ℕ} {p : Machine t s} {H H' : Fin t → ℕ} {A A' : Fin t → List Bool}
    (h : Step p cost H A H' A') (ip : ℕ) (index : List Bool) :
    Step (body p) (cost+2) (heads H ip) (data A index) (heads H' (ip+1)) (data A' index) := by
  simpa [body,heads,data,Nat.add_assoc] using (h.embed (fun _ : Fin 1=>ip) (fun _=>index)).seq (advance_run H' A' ip index)

theorem probe {t s : ℕ} (p : Machine t s) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (pre tail : List Bool) (bit : Bool) :
    Timed (loop p) 1 (entry p 0 H A pre.length (pre++bit::tail))
      (if bit then entry p 1 H A pre.length (pre++bit::tail) else final (s:=s) H A pre.length (pre++bit::tail)) := by
  have hn : next 0 (programs p 0).start
      (⟨(programs p 0).start,heads H pre.length,data A (pre++bit::tail)⟩ : Configuration (t+1) (sizes s 0)).scanned=
      if bit then some 1 else none := by
    simp [next,Configuration.scanned,heads,data,Fin.last,Fin.addCases,Streaming.read_append]
  cases bit
  · exact Timed.single (by simp [loop,entry,RecoveryCalls.machine,controlConfig,RecoveryCalls.code])
      (RecoveryCalls.stop_step (sizes s) (programs p) 0 next 0 _ (by rfl) hn)
  · exact Timed.single (by simp [loop,entry,RecoveryCalls.machine,controlConfig,RecoveryCalls.code])
      (RecoveryCalls.return_step (sizes s) (programs p) 0 next 0 1 _ (by rfl) hn)

theorem round {t s cost : ℕ} {p : Machine t s} {H H' : Fin t → ℕ} {A A' : Fin t → List Bool}
    (h : Step p cost H A H' A') (ip : ℕ) (index : List Bool) :
    ∃ time ≤ cost+3,Timed (loop p) time (entry p 1 H A ip index) (entry p 0 H' A' (ip+1) index) := by
  obtain ⟨r,hr,rh,rt,_⟩ := body_run h ip index
  obtain ⟨time,ht,tr⟩ := call_receipt (sizes s) (programs p) 0 next 1 0 _ _ r hr (by rfl)
  have same : RecoveryCalls.restarted (programs p 0) r.final.heads r.final.tapes=
      ⟨(programs p 0).start,heads H' (ip+1),data A' index⟩ := by
    apply configuration_ext
    · rfl
    · exact rh
    · exact rt
  rw [same] at tr
  exact ⟨time,by omega,tr⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek.RawLoop
