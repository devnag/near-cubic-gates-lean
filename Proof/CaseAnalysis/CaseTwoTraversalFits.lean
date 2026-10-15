import Proof.CaseAnalysis.CaseTwoTraversalNode

/-! One coarse paid capacity covers every original row field. Only the
actual flat word length, field width and bounded node count enter it; there
is no enumeration of descriptions or circuit-code numeric magnitudes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Traversal
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Fits (C F S M : ℕ) : Prop where
  source : 2*S+1≤C
  offset : S+2*F+8≤C
  count : M+1≤C
  nine : 9≤C
  field : ∀ offset width value,offset≤S → width≤F+6 → value≤width →
    FieldNative.budget offset width value+1≤C

def allocation (F S M : ℕ):=1024*(S+F+M+7)^2

theorem allocation_fits (F S M : ℕ) : Fits (allocation F S M) F S M := by
  let P:=S+F+M+7
  have hp : 7≤P:=by dsimp [P];omega
  have hS : S≤P:=by dsimp [P];omega
  have hF : F≤P:=by dsimp [P];omega
  have hM : M≤P:=by dsimp [P];omega
  change Fits (1024*P^2) F S M
  refine ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith,?_⟩
  intro offset width value hoff hw hv
  have hvP : value+1≤P:=by dsimp [P];omega
  have hwP : width≤P:=by dsimp [P];omega
  have hb:=PCPPNativeNaturalAppend.budget_bound value
  have hs:=Nat.pow_le_pow_left hvP 2
  change RankSlice.sliceBudget offset width+1+PCPPNativeNaturalAppend.budget value+1≤1024*P^2
  unfold RankSlice.sliceBudget
  nlinarith

theorem tag_width (value : Fin 6) : natBitLength value.val≤3:=by
  fin_cases value <;> decide

theorem field_budget (C F S M offset value : ℕ) (h : Fits C F S M)
    (ho : offset≤S) (hv : value≤F) : FieldStep.budget offset F value C≤16*(C+1):=by
  have hn:=h.field offset F value ho (by omega) hv
  have hr:=h.offset
  unfold FieldStep.budget FieldClear.budget FieldReady.budget
  omega

theorem node_budget (C F S M count offset a b : ℕ) (value : Fin 6)
    (h : Fits C F S M) (ho : offset+F≤S) (hc : count≤M) (ha : a≤F) (hb : b≤F) :
    nodeBudget C F count offset value.val a b≤128*(C+1):=by
  have h1:=field_budget C F S M offset a h (by omega) ha
  have h2:=field_budget C F S M (offset+F) b h ho hb
  have h3:=tag_width value
  have h4:=h.count
  unfold nodeBudget argumentsBudget TagPublish.budget NativeCopy.budget
  omega

theorem tag_budget (C : ℕ) : TagReady.budget C≤34*(C+1):=by
  unfold TagReady.budget TagReady.capacity
  omega

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Traversal
