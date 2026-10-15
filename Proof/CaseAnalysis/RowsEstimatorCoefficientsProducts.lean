import Proof.Hierarchy.CompetitorMonomialTargetWidth

/-! The original monomial product and width programs accept signed natural
fractions directly. These are the same input fields and the same controllers;
no reduction to canonical rational numerator/denominator bytes is required. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalProducts CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace Products

def operands (q : CompetitorValidity.Estimate) : Fin 4 → ℕ :=
  ![q.positive,q.negative,q.denominator,0]
def input (b : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ) : Fin 67 → List Bool :=
  CompetitorRationalProducts.input (width b) b (operands q) denominator count
def contribution (q : CompetitorValidity.Estimate) (count denominator : ℕ) : CompetitorValidity.Estimate :=
  ⟨q.positive*count,q.negative*count,q.denominator*denominator⟩

theorem contribution_value (q : CompetitorValidity.Estimate) (count denominator : ℕ) :
    (contribution q count denominator).value=q.value*((count : ℚ)/denominator) := by
  unfold contribution CompetitorValidity.Estimate.value
  push_cast
  rw [← sub_mul,← div_mul_div_comm]

theorem monomial_run (b : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ)
    (hp : q.positive<2^b) (hn : q.negative<2^b) (hq : q.denominator<2^b)
    (hc : count<2^b) (hd : denominator<2^b) :
    ∃ out,ClockJoin.ReadyRun productsProgram (2000*(b+1)^2) (input b q count denominator) out ∧
      out 10=frame (binary (width b) (contribution q count denominator).positive) ∧
      out 24=frame (binary (width b) (contribution q count denominator).negative) ∧
      out 38=frame (binary (width b) (contribution q count denominator).denominator) ∧
      (∀ j : Fin 7,out (shared j)=input b q count denominator (shared j)) := by
  have hnums : ∀ i,operands q i<2^b := by
    intro i
    fin_cases i
    · exact hp
    · exact hn
    · exact hq
    · positivity
  obtain ⟨out,hr,hstore⟩ := products_run b (operands q) denominator count hnums hd hc
  refine ⟨out,ClockJoin.enlarge productsProgram _ _ _ _ hr (CompetitorMonomialProducts.products_bound b),?_,?_,?_,hstore.shared⟩
  · exact hstore.products 0 (by decide)
  · exact hstore.products 1 (by decide)
  · exact hstore.products 2 (by decide)

theorem contribution_valid (b : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ)
    (hq : q.Valid b) (hc : count<2^b) (hd : denominator<2^b) (hdpos : 0<denominator) :
    (contribution q count denominator).Valid (width b) :=
  ⟨CompetitorMonomialTarget.product_fit b _ _ hq.positive hc,
    CompetitorMonomialTarget.product_fit b _ _ hq.negative hc,
    CompetitorMonomialTarget.product_fit b _ _ hq.denominator hd,
    Nat.mul_pos hq.denominatorPositive hdpos⟩

end Products

namespace Target
open Products CompetitorMonomialTarget CompetitorReusableDecision

def input (b t : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ) (out : List Bool) : Fin 75 → List Bool := fun i =>
  if h : i.val<67 then Products.input b q count denominator ⟨i.val,h⟩
  else if i.val=67 then List.replicate (width t) true else if i.val=74 then out else []

theorem prepare_run (b t : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ) (pre : List Bool)
    (hp : q.positive<2^b) (hn : q.negative<2^b) (hq : q.denominator<2^b)
    (hc : count<2^b) (hd : denominator<2^b) (htarget : width b≤t) :
    ∃ r out,runFrom prepareProgram (prepareBudget b t)
        (RecoveryCalls.restarted prepareProgram (heads pre) (input b t q count denominator pre))=some r ∧
      r.steps≤prepareBudget b t ∧ r.final.heads=heads pre ∧ r.final.tapes=out ∧
      out 68=frame (binary (width t) (contribution q count denominator).positive) ∧
      out 71=frame (binary (width t) (contribution q count denominator).negative) ∧
      out 38=frame (binary (width b) (contribution q count denominator).denominator) ∧
      out 70=List.replicate (2*width t+1) false ∧ out 74=pre := by
  obtain ⟨products,hproducts,hp10,hp24,hp38,_⟩ := monomial_run b q count denominator hp hn hq hc hd
  have hh : ∀ i,heads pre (native i)=0 := by
    intro i
    simp [heads,native,show i.val≠74 by omega]
  have ht : ∀ i,input b t q count denominator pre (native i)=Products.input b q count denominator i := by
    intro i
    simp [input,native,i.isLt]
  obtain ⟨first,hfirst,hfh,hft,hfs⟩ := bounded_focused_run native native_injective _ _ _ hproducts
    (heads pre) (input b t q count denominator pre) hh ht
  let produced := install native (input b t q count denominator pre) products
  obtain ⟨widened,hw,_,hw3,hw6,hw5⟩ := CompetitorNumeratorWiden.widen_run (width b) (width t)
    (contribution q count denominator).positive (contribution q count denominator).negative
    (htarget.trans (by unfold width; omega)) (product_fit b _ _ hp hc) (product_fit b _ _ hn hc)
  have hwh : ∀ i,heads pre (widenSlots i)=0 := by intro i; fin_cases i <;> rfl
  have hwt : ∀ i,produced (widenSlots i)=CompetitorNumeratorWiden.input (width b) (width t)
      (contribution q count denominator).positive (contribution q count denominator).negative i := by
    intro i
    fin_cases i
    · exact install_other native _ _ 67 (fun j => native_other j 67 (by decide))
    · exact (install_slot native native_injective _ products 10).trans hp10
    · exact (install_slot native native_injective _ products 24).trans hp24
    · exact install_other native _ _ 68 (fun j => native_other j 68 (by decide))
    · exact install_other native _ _ 69 (fun j => native_other j 69 (by decide))
    · exact install_other native _ _ 70 (fun j => native_other j 70 (by decide))
    · exact install_other native _ _ 71 (fun j => native_other j 71 (by decide))
    · exact install_other native _ _ 72 (fun j => native_other j 72 (by decide))
    · exact install_other native _ _ 73 (fun j => native_other j 73 (by decide))
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := bounded_focused_run widenSlots (by decide) _ _ _ hw (heads pre) produced hwh hwt
  have he : Composition.restart first.final widenProgram.start=RecoveryCalls.restarted widenProgram (heads pre) produced := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hl' : runFrom widenProgram (8*width t+9) (Composition.restart first.final widenProgram.start)=some last := by
    rw [he]
    exact hlast
  have hall := Composition.run_join CompetitorMonomialTarget.productsProgram widenProgram _ _ _ first last hfirst hl'
  have hcost : 2000*(b+1)^2+1+(8*width t+9)=prepareBudget b t := by unfold prepareBudget; omega
  rw [hcost] at hall
  refine ⟨Composition.joinedReceipt first last,install widenSlots produced widened,hall,?_,hlh,hlt,?_,?_,?_,?_,?_⟩
  · change first.steps+1+last.steps≤prepareBudget b t
    omega
  · exact (install_slot widenSlots (by decide) _ widened 3).trans hw3
  · exact (install_slot widenSlots (by decide) _ widened 6).trans hw6
  · exact (install_other widenSlots _ _ 38 (by decide)).trans
      ((install_slot native native_injective _ products 38).trans hp38)
  · exact (install_slot widenSlots (by decide) _ widened 5).trans hw5
  · exact (install_other widenSlots _ _ 74 (by decide)).trans
      (install_other native _ _ 74 (fun j => native_other j 74 (by decide)))

end Target
end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients
