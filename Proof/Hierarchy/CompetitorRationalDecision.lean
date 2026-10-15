import Proof.Hierarchy.CompetitorRationalProducts
import Proof.Hierarchy.CompetitorSignedDecision

/-! Enclosing paid rational decision: four ordinary binary multiplications,
two additions and a signed comparison, with all handoffs and cursor resets.
Only polynomial-width scalars enter this machine. The input contains each
denominator once; no table, child-tuple count or denominator approximation
enters the decision. -/
namespace NearCubicWires.RepairOrdinary.CompetitorRationalDecision
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def pairProgram := Composition.machine (program 0) (program 1)
noncomputable def tripleProgram := Composition.machine pairProgram (program 2)
noncomputable def productsProgram := Composition.machine tripleProgram (program 3)
def decisionSlots : Fin 8 → Fin 67 := ![10,24,38,52,63,64,65,66]
noncomputable def decisionProgram := RecoveryFocus.machine decisionSlots CompetitorSignedDecision.machine
noncomputable def machine := Composition.machine productsProgram decisionProgram
def width (b : ℕ) := 2*b+2
def productsCost (w b : ℕ) := 4*cost w b+3
def totalCost (b : ℕ) := productsCost (width b) b+1+(12*width b+15)

theorem scalar_fit (b a : ℕ) (ha : a<2^b) : a*2^b<2^width b := by
  have hp : 0<2^b := by positivity
  have h := Nat.mul_lt_mul_of_pos_right ha hp
  have he : 2^width b=4*(2^b)*(2^b) := by
    rw [width,show 2*b+2=b+b+2 by omega,pow_add,pow_add]
    norm_num
    ring
  rw [he]
  nlinarith

theorem sum_fit (b a n d e : ℕ) (ha : a<2^b) (hn : n<2^b)
    (hd : d<2^b) (he : e<2^b) : a*e+n*d<2^width b := by
  have hp : 0<2^b := by positivity
  have h1 : a*e<2^b*2^b := Nat.mul_lt_mul_of_le_of_lt (by omega) he (by omega)
  have h2 : n*d<2^b*2^b := Nat.mul_lt_mul_of_le_of_lt (by omega) hd (by omega)
  have hw : 2^width b=4*(2^b)*(2^b) := by
    rw [width,show 2*b+2=b+b+2 by omega,pow_add,pow_add]
    norm_num
    ring
  rw [hw]
  nlinarith

theorem products_run (b : ℕ) (nums : Fin 4 → ℕ) (d e : ℕ)
    (hn : ∀ i,nums i<2^b) (hd : d<2^b) (he : e<2^b) :
    ∃ out,ClockJoin.ReadyRun productsProgram (productsCost (width b) b)
      (input (width b) b nums d e) out ∧ Store (width b) b nums d e 4 out := by
  have hfactor (i : Fin 4) : factor i d e<2^b := by
    unfold factor
    split <;> assumption
  obtain ⟨s1,h0,hs1⟩ := product_run (width b) b nums d e 0 _
    (initial_store (width b) b nums d e) (scalar_fit b (nums 0) (hn 0)) (hfactor 0)
  obtain ⟨s2,h1,hs2⟩ := product_run (width b) b nums d e 1 s1 hs1
    (scalar_fit b (nums 1) (hn 1)) (hfactor 1)
  obtain ⟨s3,h2,hs3⟩ := product_run (width b) b nums d e 2 s2 hs2
    (scalar_fit b (nums 2) (hn 2)) (hfactor 2)
  obtain ⟨s4,h3,hs4⟩ := product_run (width b) b nums d e 3 s3 hs3
    (scalar_fit b (nums 3) (hn 3)) (hfactor 3)
  have h01 := ClockJoin.join (program 0) (program 1) _ _ _ s1 s2 h0 h1
  have h012 := ClockJoin.join pairProgram (program 2) _ _ _ s2 s3 h01 h2
  have hall := ClockJoin.join tripleProgram (program 3) _ _ _ s3 s4 h012 h3
  refine ⟨s4,?_,hs4⟩
  have hc : ((cost (width b) b+1+cost (width b) b)+1+cost (width b) b)+1+cost (width b) b=
      productsCost (width b) b := by unfold productsCost; omega
  rw [hc] at hall
  exact hall

theorem decision_input (b : ℕ) (nums : Fin 4 → ℕ) (d e : ℕ)
    (tapes : Fin 67 → List Bool) (h : Store (width b) b nums d e 4 tapes) (j : Fin 8) :
    tapes (decisionSlots j)=CompetitorSignedDecision.input (width b)
      (nums 0*e) (nums 1*e) (nums 2*d) (nums 3*d) j := by
  fin_cases j
  · exact h.products 0 (by decide)
  · exact h.products 1 (by decide)
  · exact h.products 2 (by decide)
  · exact h.products 3 (by decide)
  · exact h.fresh 63 (by decide)
  · exact h.fresh 64 (by decide)
  · exact h.fresh 65 (by decide)
  · exact h.fresh 66 (by decide)

theorem totalCost_bound (b : ℕ) : totalCost b≤2000*(b+1)^2 := by
  simp only [totalCost,productsCost,cost,width]
  nlinarith [sq_nonneg (b : ℤ)]

theorem cross_order (nums : Fin 4 → ℕ) (d e : ℕ) (hd : 0<d) (he : 0<e) :
    nums 1*e+nums 2*d≤nums 0*e+nums 3*d ↔
      ((nums 2 : ℚ)-nums 3)/e≤((nums 0 : ℚ)-nums 1)/d := by
  have hd' : (0 : ℚ)<d := by exact_mod_cast hd
  have he' : (0 : ℚ)<e := by exact_mod_cast he
  rw [div_le_div_iff₀ he' hd']
  have hcast : nums 1*e+nums 2*d≤nums 0*e+nums 3*d ↔
      (nums 1 : ℚ)*e+(nums 2 : ℚ)*d≤(nums 0 : ℚ)*e+(nums 3 : ℚ)*d := by
    exact_mod_cast Iff.rfl
  rw [hcast]
  constructor <;> intro h <;> nlinarith

theorem rational_decision_run (b : ℕ) (nums : Fin 4 → ℕ) (d e : ℕ)
    (hn : ∀ i,nums i<2^b) (hd : d<2^b) (he : e<2^b) (hdpos : 0<d) (hepos : 0<e) :
    ∃ out,ClockJoin.ReadyRun machine (2000*(b+1)^2) (input (width b) b nums d e) out ∧
      (∀ j : Fin 7,out (shared j)=input (width b) b nums d e (shared j)) ∧
      (readTapeBit (out 65) 0=true ↔
        ((nums 2 : ℚ)-nums 3)/e≤((nums 0 : ℚ)-nums 1)/d) := by
  obtain ⟨middle,hm,hstore⟩ := products_run b nums d e hn hd he
  have hleft := sum_fit b (nums 0) (nums 3) d e (hn 0) (hn 3) hd he
  have hright := sum_fit b (nums 1) (nums 2) d e (hn 1) (hn 2) hd he
  obtain ⟨r,hr,ht,hh,hs⟩ := CompetitorSignedDecision.signed_decision_run (width b)
    (nums 0*e) (nums 1*e) (nums 2*d) (nums 3*d) hleft hright
  let localOut := CompetitorSignedDecision.output (width b)
    (nums 0*e) (nums 1*e) (nums 2*d) (nums 3*d)
  have hdready : ClockJoin.ReadyRun CompetitorSignedDecision.machine (12*width b+15)
      (CompetitorSignedDecision.input (width b) (nums 0*e) (nums 1*e) (nums 2*d) (nums 3*d)) localOut :=
    ⟨r,hr,ht,hh,hs.le⟩
  have hf := bounded_focus decisionSlots (by decide) _ _ _ hdready middle
    (decision_input b nums d e middle hstore)
  let out := install decisionSlots middle localOut
  have hall : ClockJoin.ReadyRun machine (totalCost b) (input (width b) b nums d e) out :=
    ClockJoin.join productsProgram decisionProgram _ _ _ middle out hm hf
  refine ⟨out,ClockJoin.enlarge machine (totalCost b) _ _ out hall (totalCost_bound b),?_,?_⟩
  · intro j
    have hother : ∀ k,decisionSlots k≠shared j := by
      intro k heq
      have hv := congrArg Fin.val heq
      fin_cases k <;> simp [decisionSlots,shared] at hv <;> omega
    exact (install_other decisionSlots middle localOut (shared j) hother).trans (hstore.shared j)
  · have h65 : out 65=localOut 6 := install_slot decisionSlots (by decide) middle localOut 6
    rw [h65]
    change decide (nums 1*e+nums 2*d≤nums 0*e+nums 3*d)=true ↔ _
    rw [decide_eq_true_eq]
    exact cross_order nums d e hdpos hepos

end NearCubicWires.RepairOrdinary.CompetitorRationalDecision
