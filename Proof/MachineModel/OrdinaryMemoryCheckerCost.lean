import Proof.MachineModel.OrdinaryMemoryChecker

/-! Whole ordinary memory-checker cost at the U consumer. The external
framing, sorting, both reset stages, key production and record loop are all
included: linear in event count and quadratic in field width. -/
namespace NearCubicWires.RepairOrdinary.MemoryChecker
open LocalBitMultitape MemoryLog MemorySort StablePartition RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem record_count (req : Request) : req.sortRequest.records.length = req.count := by
  simp [Request.sortRequest, request, DominanceSort.fixedRequest]

theorem record_width (req : Request) : ∀ r ∈ req.sortRequest.records,
    (word r).length = 2*(req.indexBits+2) := by
  intro r hr
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
  rw [encoded_width]
  omega

theorem width_le (req : Request) : SortPreparation.width req.sortRequest.records ≤
    2*(req.indexBits+2) := by
  cases he : req.sortRequest.records with
  | nil => simp [SortPreparation.width, SortPreparation.firstWord]
  | cons r rs =>
    have h := record_width req r (by simp [he])
    simpa [SortPreparation.width, SortPreparation.firstWord, he] using h.le

theorem whole_budget (req : Request) :
    4*req.input.length+3+rawBudget req ≤ 2048*(req.count+1)*(req.indexBits+3)^2 := by
  let K := req.indexBits+2
  have hs := SortCost.carrier_budget_le req.sortRequest
  rw [record_count] at hs
  have hw : SortPreparation.width req.sortRequest.records+1 ≤ 2*(K+1) := by
    have h := width_le req
    dsimp only [K]
    omega
  have hsort : 4*req.input.length+3+SortCarrier.budget req.sortRequest.records ≤
      512*(req.count+1)*(K+1)^2 := by
    apply hs.trans
    calc
      _ ≤ 128*(req.count+1)*(2*(K+1))^2 := by gcongr
      _ = _ := by ring
  have hc : checkBudget req ≤ 256*(req.count+1)*(K+1) := by
    change 8*K+4+1+(req.count*(240*K+182)+1) ≤ _
    nlinarith [Nat.zero_le (req.count*K)]
  have hsquare : K+1 ≤ (K+1)^2 := Nat.le_self_pow (by decide) _
  have hc' : checkBudget req ≤ 256*(req.count+1)*(K+1)^2 :=
    hc.trans (Nat.mul_le_mul_left _ hsquare)
  have hfull : 4*req.input.length+3+rawBudget req ≤
      2*(4*req.input.length+3+SortCarrier.budget req.sortRequest.records)+3+checkBudget req := by
    unfold rawBudget
    omega
  have hpos : 1 ≤ (req.count+1)*(K+1)^2 := by
    have : 0 < (req.count+1)*(K+1)^2 := by positivity
    omega
  have hbound : 4*req.input.length+3+rawBudget req ≤ 2048*(req.count+1)*(K+1)^2 := by
    nlinarith
  simpa only [K, Nat.add_assoc] using hbound

noncomputable def boundedCarrier : WordFunction Request Request.input (fun req => [req.result])
    (fun req => 2048*(req.count+1)*(req.indexBits+3)^2) :=
  carrier.enlargeBudget whole_budget

end NearCubicWires.RepairOrdinary.MemoryChecker
