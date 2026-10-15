import Proof.CaseAnalysis.RowsRawAtomReusable
import Proof.CaseAnalysis.RowsEstimatorSubstitutionFactorLayout

/-! The original family cache has one polynomial per sum. Its actual
reader returns both cache and appended atom cursors before multiplication. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalCache
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsRawAtomSeek CloseoutRowsEstimator
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := MaskedReset.machine CloseoutRowsRawAtomReusable.machine (fun i=>decide (i=2))
def capacity (cs : List (List (List ℕ))) := 64*((cacheWord cs).length+cs.length+2)+2
def budget (cs : List (List (List ℕ))) (i : ℕ) (hi : i < cs.length) :=
  2*CloseoutRowsRawAtomReusable.budget (cs.take i) cs[i]+2

theorem run (C : ℕ) (cs : List (List (List ℕ))) (i : ℕ) (hi : i < cs.length)
    (pre tail : List Bool) (hc : capacity cs ≤ C) :
    Step machine (budget cs i hi) (SubstitutionCache.heads pre.length)
      (SubstitutionCache.data C (pre++ExtIncidence.block i++tail) (cacheWord cs) [])
      (SubstitutionCache.heads (pre.length+(ExtIncidence.block i).length))
      (SubstitutionCache.data C (pre++ExtIncidence.block i++tail) (cacheWord cs) (ExtIncidence.stream cs[i])) := by
  have cap : CloseoutRowsRawAtomReusable.capacityBound cs ≤ C := by
    unfold CloseoutRowsRawAtomReusable.capacityBound capacity at *
    omega
  have b:=CloseoutRowsRawAtomReusable.read_budget cs i hi
  have hb : CloseoutRowsRawAtomReusable.budget (cs.take i) cs[i] ≤ C := by
    unfold CloseoutRowsRawAtomReusable.budget CloseoutRowsRawAtomReusable.capacityBound capacity at *
    omega
  have raw:=CloseoutRowsRawAtomReusable.cache_run C cs i hi pre tail [] cap
  simp only [List.nil_append] at raw
  have padded:=raw.pad (SubstitutionCache.pads C)
  have masked:=padded.mask (cap:=C) (fun j=>decide (j=2)) (by
    intro j hj
    have he : j=2:=of_decide_eq_true hj
    subst j;rfl) hb
  apply (masked.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext j;fin_cases j
  all_goals simp [SubstitutionCache.heads,SubstitutionCache.data,SubstitutionCache.pads,
    CloseoutRowsRawAtomReusable.heads,CloseoutRowsRawAtomReusable.data,Fin.addCases,ZeroPadding.pad_zero]

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalCache
