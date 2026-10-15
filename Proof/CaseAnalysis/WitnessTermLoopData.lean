import Proof.CaseAnalysis.WitnessTermEnvironment
import Proof.CaseAnalysis.RowsFamilyLoop

/-! The counted loop addresses the same canonical term fields and exact
mass prefixes. Only accepted prefixes reach a later physical iteration. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermLoop
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def emitted (f : List Bool → List Bool) (words : List (List Bool)) (initial : List Bool) (j : ℕ) :=
  initial++(words.take j).flatMap f
def coefficientWord (C : ℕ) (bits : List Bool) :=
  TermRecord.word (natBitLength C) (TermChoice.rational (natBitLength C) bits)
def magnitude (C : ℕ) (bits : List Bool) := Mass.magnitude (TermChoice.rational (natBitLength C) bits)
def mass (C : ℕ) (words : List (List Bool)) (j : ℕ) := folded zero ((words.take j).map (magnitude C))
def position (words : List (List Bool)) (pre : List Bool) (j : ℕ) :=
  pre.length+((words.take j).flatMap frame).length

theorem emitted_succ (f : List Bool → List Bool) (words : List (List Bool)) (initial : List Bool)
    (j : ℕ) (hj : j<words.length) :
    emitted f words initial (j+1)=emitted f words initial j++f (words.getD j []) := by
  simp only [emitted,List.take_succ_eq_append_getElem hj,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,List.append_assoc,List.getD_eq_getElem words [] hj]

theorem position_succ (words : List (List Bool)) (pre : List Bool) (j : ℕ) (hj : j<words.length) :
    position words pre (j+1)=position words pre j+2*(words.getD j []).length+1 := by
  simp only [position,CloseoutRowsFamilyLoop.next_word words [] frame j hj,frame_length]
  omega

private theorem folded_append_one (a c : Estimate) (xs : List Estimate) :
    folded a (xs++[c])=CompetitorRationalNumerators.add (folded a xs) c := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simpa only [List.cons_append,folded] using ih (CompetitorRationalNumerators.add a x)

theorem mass_succ (C : ℕ) (words : List (List Bool)) (j : ℕ) (hj : j<words.length) :
    mass C words (j+1)=CompetitorRationalNumerators.add (mass C words j) (magnitude C (words.getD j [])) := by
  simp only [mass,List.take_succ_eq_append_getElem hj,List.map_append,List.map_cons,List.map_nil,
    folded_append_one,List.getD_eq_getElem words [] hj]

private theorem trace_fold (B : ℕ) (a : Estimate) (xs ys : List Estimate)
    (h : Trace B a (xs++ys)) : Trace B (folded a xs) ys := by
  induction xs generalizing a with
  | nil => exact h
  | cons x xs ih => exact ih _ h.2.2

private theorem trace_start (B : ℕ) (a : Estimate) (xs : List Estimate) (h : Trace B a xs) : a.Valid B := by
  cases xs with
  | nil => exact h
  | cons x xs => exact h.1

theorem mass_valid (T C : ℕ) (words : List (List Bool)) (j : ℕ) (hk : words.length ≤ T) :
    (mass C words j).Valid (width T (natBitLength C)) := by
  have hbit : 1 ≤ natBitLength C := by simp only [natBitLength];omega
  have h := TermChoice.trace T (natBitLength C) words hbit hk
  have exactList : Mass.records (words.map (TermChoice.rational (natBitLength C)))=words.map (magnitude C) := by
    simp only [Mass.records,List.map_map,Function.comp_def]
    rfl
  rw [exactList] at h
  have split : (words.take j).map (magnitude C)++(words.drop j).map (magnitude C)=words.map (magnitude C) := by
    rw [←List.map_append,List.take_append_drop]
  have hp := trace_fold (width T (natBitLength C)) zero ((words.take j).map (magnitude C))
    ((words.drop j).map (magnitude C)) (by rw [split];exact h)
  exact trace_start _ _ _ hp

theorem mass_value (T C : ℕ) (words : List (List Bool)) (hk : words.length ≤ T) :
    (mass C words words.length).value=(words.map (fun bits=>|TermChoice.rational (natBitLength C) bits|)).sum := by
  have hbit : 1 ≤ natBitLength C := by simp only [natBitLength];omega
  have h := TermChoice.trace T (natBitLength C) words hbit hk
  have exactList : Mass.records (words.map (TermChoice.rational (natBitLength C)))=words.map (magnitude C) := by
    simp only [Mass.records,List.map_map,Function.comp_def]
    rfl
  rw [exactList] at h
  have v := folded_value (width T (natBitLength C)) zero (words.map (magnitude C)) h
  have hz : zero.value=0 := by norm_num [zero,Estimate.value]
  rw [hz,zero_add] at v
  have sumEq : ((words.map (magnitude C)).map Estimate.value).sum=
      (words.map (fun bits=>|TermChoice.rational (natBitLength C) bits|)).sum := by
    simp only [List.map_map,Function.comp_def,magnitude,Mass.magnitude_value]
  rw [sumEq] at v
  simpa only [mass,List.take_length] using v

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.TermLoop
