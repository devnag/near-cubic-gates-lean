import Proof.CaseAnalysis.RowsRawPairReusable

/-! The shared Pair cache supplies an atom at head zero, beside the live source cursor. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionCache
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
open CloseoutRowsRawPairSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=MaskedReset.machine CloseoutRowsRawPairReusable.machine (fun i=>decide (i=2))
def heads (pos : ℕ) : Fin 7 → ℕ:=![pos,0,0,0,0,0,0]
def data (C : ℕ) (index cache atom : List Bool) : Fin 7 → List Bool:=
  ![index,cache,ZeroPadding.pad C atom,[false],List.replicate C false,List.replicate C false,List.replicate C false]
def pads (C : ℕ) (i : Fin 6) : ℕ:=if i=2 then C else 0
def budget (cs : List Pair) (i : ℕ) (hi : i<cs.length):=
  2*CloseoutRowsRawPairReusable.budget (cs.take i) cs[i]+2
def capacity (cs : List Pair):=128*((cacheWord cs).length+cs.length+2)+2

theorem run (C : ℕ) (cs : List Pair) (i : ℕ) (hi : i<cs.length) (pre tail : List Bool)
    (hc : capacity cs ≤ C) :
    Step machine (budget cs i hi) (heads pre.length)
      (data C (pre++ExtIncidence.block i++tail) (cacheWord cs) [])
      (heads (pre.length+(ExtIncidence.block i).length))
      (data C (pre++ExtIncidence.block i++tail) (cacheWord cs) (ExtIncidence.stream (cs[i].1++cs[i].2))) := by
  have hc0 : CloseoutRowsRawPairReusable.capacityBound cs ≤ C := by
    unfold CloseoutRowsRawPairReusable.capacityBound capacity at *
    omega
  have hb : CloseoutRowsRawPairReusable.budget (cs.take i) cs[i] ≤ C :=
    (CloseoutRowsRawPairReusable.logical_budget cs i hi).trans hc
  have raw:=CloseoutRowsRawPairReusable.cache_run C cs i hi pre tail [] hc0
  simp only [List.nil_append] at raw
  have padded:=raw.pad (pads C)
  have masked:=padded.mask (cap:=C) (fun j=>decide (j=2)) (by
    intro j hj
    have he : j=2:=of_decide_eq_true hj
    subst j;rfl) hb
  apply (masked.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext j;fin_cases j
  all_goals simp [heads,data,pads,CloseoutRowsRawPairReusable.heads,CloseoutRowsRawPairReusable.data,
    Fin.addCases,ZeroPadding.pad_zero]

theorem budget_bound (cs : List Pair) (i : ℕ) (hi : i<cs.length) :
    budget cs i hi ≤ 256*((cacheWord cs).length+cs.length+2)+6 := by
  have h:=CloseoutRowsRawPairReusable.logical_budget cs i hi
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionCache
