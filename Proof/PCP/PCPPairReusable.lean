import Proof.PCP.PCPSerializerMass
import Proof.Amplification.RecoveryTapeSupport

/-! Canonical pair execution in already-cleared finite workspace. The
enclosing traversal pays its erase and loads the two operands; this call
preserves a common allocation bound and returns the trimmed framed result. -/
namespace NearCubicWires.RepairOrdinary.PCPPairReusable
open LocalBitMultitape RecoveryExecution RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem pad_nested (large small : ℕ) (bits : List Bool) (h : small ≤ large) :
    ZeroPadding.pad large (ZeroPadding.pad small bits)=ZeroPadding.pad large bits := by
  unfold ZeroPadding.pad
  simp only [List.length_append,List.length_replicate,List.append_assoc]
  rw [←List.replicate_add]
  congr 2
  omega

theorem padded_ready {t s fuel : ℕ} (p : Machine t s) (input output : Fin t → List Bool)
    (h : ClockJoin.ReadyRun p fuel input output) (caps : Fin t → ℕ) :
    ClockJoin.ReadyRun p fuel (fun i => ZeroPadding.pad (caps i) (input i))
      (fun i => ZeroPadding.pad (caps i) (output i)) := by
  obtain ⟨base,hr,ht,hh,hs⟩ := h
  obtain ⟨r,hrun,hf,hsteps,_⟩ := ZeroPadding.run_config p caps _ _ base hr
  refine ⟨r,hrun,?_,?_,hsteps.trans_le hs⟩
  · rw [hf]
    funext i
    change ZeroPadding.pad (caps i) (base.final.tapes i)=_
    rw [ht]
  · intro i
    rw [hf]
    exact hh i

def input (cap : ℕ) (left right : List Bool) : Fin 38 → List Bool :=
  fun i => ZeroPadding.pad cap (PCPPairCanonical.input left right i)

theorem pair_run (cap : ℕ) (left right : List Bool)
    (hpos : 0<Nat.pair (value left) (value right))
    (hcap : PCPPairCanonical.budget left right+1 ≤ cap) :
    ∃ out : Fin 38 → List Bool,
      ClockJoin.ReadyRun PCPPairCanonical.machine (PCPPairCanonical.budget left right)
        (input cap left right) out ∧
      out 26=ZeroPadding.pad cap (frame (Nat.pair (value left) (value right)).bits) ∧
      (∀ i,(out i).length ≤ cap) := by
  obtain ⟨cold,hcold,hfield,_⟩ := PCPPairCanonical.pair_run left right hpos
  have hwidth : 2*PCPPair.width left right+1 ≤ cap := by
    unfold PCPPairCanonical.budget PCPPairCold.budget PCPPair.budget at hcap
    omega
  have hlen : 2*left.length+1 ≤ cap ∧ 2*right.length+1 ≤ cap := by
    unfold PCPPair.width at hwidth
    constructor <;> omega
  have hpad := padded_ready _ _ _ hcold (fun _ => cap)
  obtain ⟨r,hr,ht,hh,hs⟩ := hpad
  have hi : ∀ i,(input cap left right i).length ≤ max cap (0+1) := by
    intro i
    simp only [input,ZeroPadding.pad_length,PCPPairCanonical.input]
    split
    · rw [frame_length]
      omega
    · split
      · rw [frame_length]
        omega
      · simp
  have hsupport := RecoveryTapeSupport.run_support PCPPairCanonical.machine _ _ r hr cap 0
    (by intro i; exact Nat.zero_le _) hi
  refine ⟨_,⟨r,hr,ht,hh,hs⟩,?_,?_⟩
  · rw [hfield]
    exact pad_nested cap _ _ hwidth
  · intro i
    have h := hsupport i
    rw [ht] at h
    simpa only [Nat.zero_add,max_eq_left (by omega : r.steps+1 ≤ cap)] using h

def capacity (bytes : ℕ) : ℕ := 131072*(bytes+1)^10

theorem capacity_covers (bytes : ℕ) (left right : List Bool)
    (hl : left.length ≤ 3*(bytes+1)^5) (hr : right.length ≤ 3*(bytes+1)^5) :
    PCPPairCanonical.budget left right+1 ≤ capacity bytes := by
  have hbudget := PCPPairCanonical.budget_quadratic left right
  have hpow : 1 ≤ (bytes+1)^5 := Nat.one_le_pow 5 _ (by omega)
  have hsum : left.length+right.length+1 ≤ 7*(bytes+1)^5 := by omega
  have hsquare := Nat.pow_le_pow_left hsum 2
  have he : (7*(bytes+1)^5)^2=49*(bytes+1)^10 := by ring
  rw [he] at hsquare
  have hp : 1 ≤ (bytes+1)^10 := Nat.one_le_pow 10 _ (by omega)
  unfold capacity
  omega

end NearCubicWires.RepairOrdinary.PCPPairReusable
