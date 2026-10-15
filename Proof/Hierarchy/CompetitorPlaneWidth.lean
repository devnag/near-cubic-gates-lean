import Proof.Hierarchy.CompetitorPlaneSign

/-! The literal 2p-plane scheduler admits one common width b+2p+2.
This includes every internal shifted multiplicand, not merely its final
product. The actual pass returns the bounded next P/N stream for iteration. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlaneWidth
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
open CompetitorPlaneStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def width (b p : ℕ) := b+2*p+2
def unit (b p : ℕ) := 2^(b+p)
def factor (t : ℕ) : List Bool := List.replicate t false++[true]
def update (sign : Bool) (t : ℕ) (a : Cell) : Cell :=
  ⟨a.count,CompetitorPlane.nextPositive sign a.positive a.count (factor t),
    CompetitorPlane.nextNegative sign a.negative a.count (factor t)⟩
def Bounded (b p j : ℕ) (a : Cell) : Prop :=
  a.count<2^b ∧ a.positive+a.negative≤j*unit b p

@[simp] theorem factor_length (t : ℕ) : (factor t).length=t+1 := by simp [factor]
@[simp] theorem factor_value (t : ℕ) : value (factor t)=2^t := by
  simp [factor,value_append,value]

theorem total_fit (b p j : ℕ) (hj : j≤2*p) : j*unit b p<2^width b p := by
  have hp : p<2^p := Nat.lt_two_pow_self
  have hjp : j<2^(p+2) := by
    simp only [pow_add,pow_two] at *
    nlinarith
  have hmul := Nat.mul_lt_mul_of_pos_right hjp (show 0<unit b p by unfold unit; positivity)
  have he : 2^(p+2)*unit b p=2^width b p := by
    unfold unit width
    rw [← pow_add]
    congr 1
    omega
  simpa only [he] using hmul

theorem update_sum (sign : Bool) (t : ℕ) (a : Cell) :
    (update sign t a).positive+(update sign t a).negative=
      a.count*2^t+(a.positive+a.negative) := by
  cases sign <;> simp [update,CompetitorPlane.nextPositive,CompetitorPlane.nextNegative,Nat.add_assoc,Nat.add_left_comm]

theorem contribution_bound (b p t count : ℕ) (ht : t<p) (hc : count<2^b) :
    count*2^t≤unit b p := by
  have hpow : 2^t≤2^p := Nat.pow_le_pow_right (by omega) (by omega)
  have hmul := Nat.mul_le_mul hc.le hpow
  simpa [unit,pow_add] using hmul

theorem bounded_update (sign : Bool) (b p j t : ℕ) (a : Cell)
    (ht : t<p) (ha : Bounded b p j a) :
    Bounded b p (j+1) (update sign t a) := by
  refine ⟨ha.1,?_⟩
  rw [update_sum]
  have hm := contribution_bound b p t a.count ht ha.1
  nlinarith [ha.2]

theorem cell_valid (sign : Bool) (b p j t : ℕ) (a : Cell)
    (hj : j<2*p) (ht : t<p) (ha : Bounded b p j a) :
    a.Valid sign b (width b p) (factor t) := by
  have hp := total_fit b p j (by omega)
  have hn := total_fit b p (j+1) (by omega)
  have ha' := bounded_update sign b p j t a ht ha
  have hshift : a.count*2^(t+1)<unit b p := by
    have hp' : 2^(t+1)≤2^p := Nat.pow_le_pow_right (by omega) (by omega)
    have hc := Nat.mul_lt_mul_of_pos_right ha.1 (show 0<2^(t+1) by positivity)
    have hm := Nat.mul_le_mul_left (2^b) hp'
    have he : 2^b*2^p=unit b p := by simp [unit,pow_add]
    rw [he] at hm
    omega
  have hu : unit b p<2^width b p := by simpa only [one_mul] using total_fit b p 1 (by omega)
  have haSum := ha.2
  refine ⟨ha.1,by omega,by omega,?_,?_⟩
  · simpa only [factor_length] using hshift.trans hu
  · have hsum := (ha'.2).trans_lt hn
    rw [update_sum] at hsum
    simp only [factor_value]
    cases sign <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega

theorem output_word (sign : Bool) (w t : ℕ) (xs : List Cell) :
    newWords sign w (factor t) xs=oldWords w (xs.map (update sign t)) := by
  simp only [newWords,oldWords,List.flatMap_map]
  rfl

theorem bounded_plane_run (sign : Bool) (b p j t : ℕ) (xs : List Cell)
    (hj : j<2*p) (ht : t<p) (hx : ∀ a∈xs,Bounded b p j a) :
    ∃ out,ClockJoin.ReadyRun CompetitorPlaneSign.machine
      (CompetitorPlaneSign.budget (width b p) xs.length)
      (CompetitorPlaneSign.input sign b (width b p) (factor t) xs) out ∧
      out 17=oldWords (width b p) (xs.map (update sign t)) ∧
      out 18=countWords b xs ∧ out 19=oldWords (width b p) xs ∧
      (∀ a∈xs.map (update sign t),Bounded b p (j+1) a) := by
  obtain ⟨out,hr,h17,h18,h19,_⟩ := CompetitorPlaneSign.run_plane sign b (width b p) (factor t) xs
    (by unfold width; omega) (by simp only [factor_length]; unfold width; omega)
    (fun a ha => cell_valid sign b p j t a hj ht (hx a ha))
  refine ⟨out,hr,(h17.trans (output_word sign (width b p) t xs)),h18,h19,?_⟩
  intro a ha
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
  exact bounded_update sign b p j t v ht (hx v hv)

end NearCubicWires.RepairOrdinary.CompetitorPlaneWidth
