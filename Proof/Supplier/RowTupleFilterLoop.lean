import Proof.Supplier.RowTupleFilterMeaning

/-! The retained unary degree driver executes one checked digit body per
digit. Only the short degree is unary; the tuple enumeration count is binary. -/
namespace NearCubicWires.RepairOrdinary.RowTupleFilterLoop
open LocalBitMultitape RecoveryExecution RowTupleFilterParts RowTupleFilterBody
open RowTupleFilterMeaning SignedSortKey RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def word (w : ℕ) (ds : List ℕ) := ds.flatMap (fun d=>Streaming.marks (binary w d))
noncomputable def machine := RepeatMachine.machine RowTupleFilterBody.machine (fun _ _=>true)
noncomputable def cfg (phase : Fin 5) (pos driver w k : ℕ) (x : Data) :=
  RepeatMachine.cfg phase (RowTupleFilterParts.cfg RowTupleFilterBody.machine.start pos w x) k driver

theorem word_length (w : ℕ) (ds : List ℕ) : (word w ds).length=2*w*ds.length := by
  simp [word,Streaming.marks_length,Nat.mul_comm]

theorem remaining (w k j : ℕ) (ds : List ℕ) (x : Data) (pre tail : List Bool)
    (hj : j+ds.length=k) (hx : x.source=pre++word w ds++tail)
    (hd : ∀ d∈ds,d<2^w) (hb : x.bound<2^w) (hp : x.previous<2^w) :
    Timed machine (ds.length*(20*w+33)+k+3)
      (cfg 0 pre.length (j+1) w k x)
      (cfg 3 (pre.length+(word w ds).length) 1 w k (fold x ds)) := by
  induction ds generalizing j x pre with
  | nil =>
    have he : j=k := by simpa using hj
    subst j
    simpa only [List.length_nil,zero_mul,zero_add,word,List.flatMap_nil,Nat.add_zero,fold,machine,cfg] using
      RepeatMachine.exhaust RowTupleFilterBody.machine (fun _ _=>true)
        (RowTupleFilterParts.cfg RowTupleFilterBody.machine.start pre.length w x) k
  | cons d ds ih =>
    have hd0 := hd d (by simp)
    have hsource : x.source=pre++Streaming.marks (binary w d)++(word w ds++tail) := by
      simpa only [word,List.flatMap_cons,List.append_assoc] using hx
    obtain ⟨r,hr,rh,rt,rs⟩ := body_run pre (word w ds++tail) w d x hsource hd0 hb hp
    have ht := RepeatMachine.iteration RowTupleFilterBody.machine (fun _ _=>true)
      (RowTupleFilterParts.cfg RowTupleFilterBody.machine.start pre.length w x) k j r
      (by rfl) (by simp only [List.length_cons] at hj; omega) hr
    simp only [↓reduceIte] at ht
    have he := RowOccurrenceLoop.cfg_eq 0 r.final
      (RowTupleFilterParts.cfg RowTupleFilterBody.machine.start (pre.length+2*w) w (advance x d))
      k (j+2) rh rt
    rw [he] at ht
    have hnextsource : (advance x d).source=(pre++Streaming.marks (binary w d))++word w ds++tail := by
      rw [(advance_fields x d).1,hsource]
      simp only [List.append_assoc]
    have htail := ih (j+1) (advance x d) (pre++Streaming.marks (binary w d))
      (by simp only [List.length_cons] at hj; omega) hnextsource
      (fun a ha=>hd a (List.mem_cons_of_mem _ ha)) hb hd0
    simp only [List.length_append,Streaming.marks_length,binary_length] at htail
    have hdri : j+1+1=j+2 := by omega
    rw [hdri] at htail
    have whole := ht.trans htail
    have htime : r.steps+2+(ds.length*(20*w+33)+k+3)=(d::ds).length*(20*w+33)+k+3 := by
      rw [rs,List.length_cons]
      ring
    rw [htime] at whole
    have hpos : pre.length+2*w+(word w ds).length=pre.length+(word w (d::ds)).length := by
      simp only [word,List.flatMap_cons,List.length_append,Streaming.marks_length,binary_length]
      omega
    simpa only [machine,cfg,fold,hpos] using whole

theorem scan_run (w : ℕ) (ds : List ℕ) (x : Data) (tail : List Bool)
    (hx : x.source=word w ds++tail) (hd : ∀ d∈ds,d<2^w)
    (hb : x.bound<2^w) (hp : x.previous<2^w) :
    ∃ r,runFrom machine (ds.length*(20*w+34)+3) (cfg 0 0 1 w ds.length x)=some r ∧
      r.final=cfg 3 (2*w*ds.length) 1 w ds.length (fold x ds) ∧
      r.steps=ds.length*(20*w+34)+3 := by
  have h := remaining w ds.length 0 ds x [] tail (by simp) (by simpa using hx) hd hb hp
  have he : ds.length*(20*w+33)+ds.length+3=ds.length*(20*w+34)+3 := by ring
  simp only [List.length_nil,zero_add,word_length,he] at h
  exact h.run (by simp [machine,cfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])

end NearCubicWires.RepairOrdinary.RowTupleFilterLoop
