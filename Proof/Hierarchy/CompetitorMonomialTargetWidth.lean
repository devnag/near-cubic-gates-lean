import Proof.Hierarchy.CompetitorDimensionedDecision

namespace NearCubicWires.RepairOrdinary.CompetitorMonomialTarget
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalDecision CompetitorMonomialProducts CompetitorReusableDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def native (i : Fin 67) : Fin 75 := i.castAdd 8
def widenSlots : Fin 9 → Fin 75 := ![67,10,24,68,69,70,71,72,73]
def heads (out : List Bool) : Fin 75 → ℕ := fun i => if i.val=74 then out.length else 0
def input (b t : ℕ) (q : ℚ) (count denominator : ℕ) (out : List Bool) : Fin 75 → List Bool := fun i =>
  if h : i.val<67 then CompetitorMonomialProducts.input b q count denominator ⟨i.val,h⟩
  else if i.val=67 then List.replicate (width t) true else if i.val=74 then out else []
noncomputable def productsProgram := RecoveryFocus.machine native CompetitorRationalDecision.productsProgram
noncomputable def widenProgram := RecoveryFocus.machine widenSlots CompetitorNumeratorWiden.machine
noncomputable def prepareProgram := Composition.machine productsProgram widenProgram
def prepareBudget (b t : ℕ) := 2000*(b+1)^2+8*width t+10

theorem native_injective : Function.Injective native := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 75 => a.val) h)
theorem native_other (j : Fin 67) (i : Fin 75) (hi : 67 ≤ i.val) : native j≠i := by
  intro h
  have hv := congrArg (fun a : Fin 75 => a.val) h
  change j.val=i.val at hv
  omega
theorem product_fit (b a c : ℕ) (ha : a<2^b) (hc : c<2^b) : a*c<2^width b :=
  (Nat.mul_le_mul_left a hc.le).trans_lt (scalar_fit b a ha)
theorem contribution_valid (b : ℕ) (q : ℚ) (count denominator : ℕ)
    (hp : positive q<2^b) (hn : negative q<2^b) (hq : q.den<2^b)
    (hc : count<2^b) (hd : denominator<2^b) (hdpos : 0<denominator) :
    (contribution q count denominator).Valid (width b) :=
  ⟨product_fit b _ _ hp hc,product_fit b _ _ hn hc,product_fit b _ _ hq hd,
    contribution_denominator_positive q count denominator hdpos⟩

theorem prepare_run (b t : ℕ) (q : ℚ) (count denominator : ℕ) (pre : List Bool)
    (hp : positive q<2^b) (hn : negative q<2^b) (hq : q.den<2^b)
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
  have ht : ∀ i,input b t q count denominator pre (native i)=CompetitorMonomialProducts.input b q count denominator i := by
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
  have hall := Composition.run_join productsProgram widenProgram _ _ _ first last hfirst hl'
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

end NearCubicWires.RepairOrdinary.CompetitorMonomialTarget
