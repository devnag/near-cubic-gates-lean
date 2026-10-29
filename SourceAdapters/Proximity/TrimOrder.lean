import SourceAdapters.Proximity.Trimming

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the exact sorted-list interpretation of semantic trimming.
-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary
open NearCubicGates.Published.CW19Proximity
open NearCubicGates.Adapters.Proximity

theorem sortedAddresses_eq_ofFn {n : ℕ} (V : ThreeQueryVerifier n) :
    (usedProofAddresses V).sort (· ≤ ·) =
      List.ofFn (fun i : Fin (usedProofAddresses V).card =>
        (((usedProofAddresses V).orderIsoOfFin rfl) i).val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn, Finset.coe_orderIsoOfFin_apply,
      Finset.orderEmbOfFin_apply]
    rfl

theorem denseAddress_val {n : ℕ} (V : ThreeQueryVerifier n)
    (coins : Fin (2 ^ V.randomBits)) (j : Fin 3) :
    (denseAddress V coins j).val =
      match (V.clause coins j).address with
      | .inl i => i.val
      | .inr address => n + ((usedProofAddresses V).sort (· ≤ ·)).idxOf address := by
  unfold denseAddress
  split <;> simp_all [Finset.orderIsoOfFin_symm_apply]

theorem trimmed_literalCode {n : ℕ} (V : ThreeQueryVerifier n)
    (coins : Fin (2 ^ V.randomBits)) (j : Fin 3) :
    NearCubicWires.RepairSource.literalCode ((trimVerifier V).clause coins j) =
      2 * (denseAddress V coins j).val + (V.clause coins j).negated.toNat := by
  cases h : (V.clause coins j).negated <;> simp [trimVerifier, h, NearCubicWires.RepairSource.literalCode]


/-- Boundary: no proof coordinates, with one available input coordinate. -/
def inputOnlyVerifier : ThreeQueryVerifier 1 where
  randomBits := 0
  clause := fun _ _ => ⟨.inl 0, false⟩

example : (usedProofAddresses inputOnlyVerifier).card = 0 := by decide

example : (trimVerifier inputOnlyVerifier).word =
    [false, false, false, false, false] := by decide

/-- Boundary: no input coordinates, duplicated unsorted proof addresses, and
one negated literal. Dense ranks are assigned in increasing address order. -/
def proofOnlyVerifier : ThreeQueryVerifier 0 where
  randomBits := 0
  clause := fun _ j => ⟨.inr (if j.val = 1 then 3 else 17), decide (j.val = 1)⟩

theorem proofOnly_sorted : (usedProofAddresses proofOnlyVerifier).sort (· ≤ ·) = [3, 17] := by
  have hs : usedProofAddresses proofOnlyVerifier = ([3, 17] : List ℕ).toFinset := by decide
  rw [hs]
  exact (List.toFinset_sort (r := (· ≤ ·)) (by decide : ([3, 17] : List ℕ).Nodup)).mpr (by decide)

example : (trimVerifier proofOnlyVerifier).word =
    frame [false, true] ++ frame [] ++
      frame [false, true] ++ frame [true] ++ frame [false, true] := by
  simp only [NearCubicGates.PublishedSources.PCPP.RawThreeQueryPCPP.word,
    trimmed_literalCode, denseAddress_val, proofOnly_sorted]
  decide

end NearCubicGates.Adapters.Proximity.Trim
