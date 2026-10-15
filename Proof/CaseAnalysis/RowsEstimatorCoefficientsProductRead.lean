import Proof.CaseAnalysis.RowsEstimatorCoefficientsValue

/-! The selected coefficient tuple is read in its original compact grammar.
This bank deliberately keeps the existing framed-reader and clear ports;
all factors are actual source fields and all work backing is physical. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Product
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalDecision CompetitorReusableDecision CompetitorMonomialStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fields (c : ℕ) (q : ℚ) : Fin 6 → List Bool :=
  ![[decide (q.num<0)],binary c q.num.natAbs,binary c q.den,[],[],[]]
def sources : List (Fin 6) := [0,1,2]
def record (c : ℕ) (q : ℚ) :=
  frame [decide (q.num<0)]++frame (binary c q.num.natAbs)++frame (binary c q.den)
noncomputable def loaded (b c : ℕ) (q : ℚ) (A : Fin 88 → List Bool) :=
  CompetitorMonomialStream.placed b (fields c q) sources A

structure Store (b n d : ℕ) (source : List Bool) (A : Fin 88 → List Bool) : Prop where
  source : A 79=source
  short : A 81=List.replicate b true
  wide : A 82=List.replicate (width b) true
  numerator : A 74=ZeroPadding.pad (capacity b) (frame (binary (width b) n))
  denominator : A 83=ZeroPadding.pad (capacity b) (frame (binary (width b) d))
  driver : A 84=List.replicate (capacity b) true
  log : A 85=List.replicate (capacity b+1) false
  blank : ∀ j,A (workSlot j)=List.replicate (capacity b) false

theorem record_stream (c : ℕ) (q : ℚ) : fieldStream (fields c q) sources=record c q := by
  simp [fieldStream,fields,sources,record,List.append_assoc]
theorem record_length (c : ℕ) (q : ℚ) : (record c q).length=4*c+5 := by
  simp [record]
  omega
theorem read_cost (c : ℕ) (q : ℚ) : fieldCost (fields c q) sources=8*c+16 := by
  simp [fieldCost,fields,sources]
  omega

theorem loaded_cases (b c : ℕ) (q : ℚ) (A : Fin 88 → List Bool) (i : Fin 88) :
    loaded b c q A i=
      if i.val=2 then ZeroPadding.pad (capacity b) (frame (binary c q.den))
      else if i.val=1 then ZeroPadding.pad (capacity b) (frame (binary c q.num.natAbs))
      else if i.val=0 then ZeroPadding.pad (capacity b) (frame [decide (q.num<0)]) else A i := by
  simp only [loaded,placed,sources,CompetitorMonomialStream.loaded,Function.update_apply,target,Fin.ext_iff]
  rfl

theorem read_run (b c n d : ℕ) (q : ℚ) (pre suffix : List Bool) (A : Fin 88 → List Bool)
    (h : Store b n d (pre++record c q++suffix) A) (hc : c≤b) :
    ∃ r,runFrom (fieldsProgram sources) (8*c+16)
        (cfg 0 (fieldsProgram sources).start pre.length A)=some r ∧
      r.steps=8*c+16 ∧ r.final.heads=heads 0 (pre.length+(record c q).length) ∧
      r.final.tapes=loaded b c q A := by
  have hb : ∀ j∈sources,A (target j)=List.replicate (capacity b) false := by
    intro j hj
    simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl
    · exact h.blank 0
    · exact h.blank 1
    · exact h.blank 2
  have hcap : ∀ j∈sources,2*(fields c q j).length+1≤capacity b := by
    intro j hj
    simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl <;> simp [fields]
    all_goals unfold capacity; nlinarith
  obtain ⟨r,hr,hh,ht,hs⟩ := fields_run b 0 (fields c q) sources (by decide) pre suffix A
    (by simpa only [record_stream] using h.source) hb (h.blank 78) hcap
  rw [read_cost] at hr hs
  exact ⟨r,hr,hs,by simpa only [record_stream] using hh,ht⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Product
