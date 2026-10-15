import Proof.Wire_3_5.RecoveryCaseTwo
import Proof.Wire_3_5.RecoverySetup
import Proof.Wire_3_5.LiteralSources
import Proof.Wire_3_5.LedgerLengths
import Proof.CaseAnalysis.Language

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)
open NearCubicWires.RepairSource.CloseoutLanguage (core clauseWidth)

section Language
variable (l : Literals) (G : Split.Gate)

noncomputable def recRefuter (kclk : ℕ) : HierarchyRefuterAlgorithm (fun n => n ^ (kclk + 2)) :=
  l.eightSources.hierarchy (fun n => n ^ (kclk + 2)) (PolynomialClock.ordinaryClock kclk)

/-- The hierarchy language. -/
noncomputable def recL (kclk : ℕ) : Language := fun n x => (recRefuter l kclk).hierarchy.timedView.accepts n x

theorem recL_inNTIME (kclk : ℕ) : InNTIME (fun n => n ^ (kclk + 2)) (recL l kclk) :=
  ⟨(recRefuter l kclk).hierarchy, fun n x => hierarchy_language_exact _ n x⟩

/-- The union setup at the hierarchy language. -/
noncomputable def recSetup (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) : UnionSetup (G.inputs kclk coef A a ha) :=
  unionSetupS1 l G kclk coef A a ha (recL l kclk) (recL_inNTIME l kclk)

/-- The union machine at the hierarchy language. -/
noncomputable def recMachine {kclk coef A a : ℕ} {ha : a ≤ kclk + 1} (U : Split.UnionLeafAt (G.inputs kclk coef A a ha)
    (unionSetupS1 l G kclk coef A a ha)) (P : FusedPrimitive (G.inputs kclk coef A a ha)) :
    OrdinaryWeakMachine :=
  U.build P (recL l kclk)

variable {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- The XOR schedule `t(q) + 1`. -/
def recCopies (q : ℕ) : ℕ := rowBt h0 h1 q + 1

noncomputable def recSchedule (kclk Apad dG : ℕ) : LengthSchedule :=
  let S := rowBLengthSchedule h0 h1 kclk Apad dG
  { S with
    t := fun q => S.t q + 1
    J := S.J + 1
    t_pos := fun q => by omega
    t_jump := fun q q' hcw hqq' hq' => by have := S.t_jump q q' hcw hqq' hq'; omega
    t_tendsto := Filter.tendsto_atTop_atTop.2 fun b => by
      obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.1 S.t_tendsto b
      exact ⟨N, fun q hq => by have := hN q hq; omega⟩
    t_log := fun q => by have := S.t_log q; nlinarith }

theorem recSchedule_qs (kclk Apad dG a : ℕ) : (recSchedule h0 h1 kclk Apad dG).qs a = nativeWidth kclk Apad (2 ^ a) :=
  rfl

theorem recSchedule_t (kclk Apad dG q : ℕ) : (recSchedule h0 h1 kclk Apad dG).t q = recCopies h0 h1 q := rfl

variable (dG : ℕ)

/-- **The canonical language** (D1.3): at length `n`, the core of the selected source index `a(n)` at the refuter's
output for the machine at `2^{a(n)}`, with `t(q)+1` copies and the clause width `⌈d_G log₂(q+2)⌉`. -/
noncomputable def recLanguage (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (M : OrdinaryWeakMachine) : Language :=
  fun n address =>
    let s := (recSchedule h0 h1 kclk G.Apad dG).sourceIdx n
    let q := nativeWidth kclk G.Apad (2 ^ s)
    core (recSetup l G kclk coef A a ha).pcp (gatePCPP l)
      (selectedAmplifier l.eightSources.amplification (recOracleDeg l)) ((recRefuter l kclk).output M (2 ^ s))
      (recCopies h0 h1 q) (clauseWidth dG q) n address

/-- The slice at length `n` is the core of the selected source index. -/
theorem recLanguage_slice (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (M : OrdinaryWeakMachine) (n : ℕ) :
    recLanguage l G h0 h1 dG kclk coef A a ha M n =
      core (recSetup l G kclk coef A a ha).pcp (gatePCPP l)
        (selectedAmplifier l.eightSources.amplification (recOracleDeg l))
        ((recRefuter l kclk).output M (2 ^ (recSchedule h0 h1 kclk G.Apad dG).sourceIdx n))
        (recCopies h0 h1 (nativeWidth kclk G.Apad (2 ^ (recSchedule h0 h1 kclk G.Apad dG).sourceIdx n)))
        (clauseWidth dG (nativeWidth kclk G.Apad (2 ^ (recSchedule h0 h1 kclk G.Apad dG).sourceIdx n))) n := rfl

end Language

/-! ## The refuter's rejected yes-instances -/

section Refuter
variable (l : Literals) (G : Split.Gate) {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}
  (U : Split.UnionLeafAt (G.inputs kclk coef A a ha) (unionSetupS1 l G kclk coef A a ha))
  (P : FusedPrimitive (G.inputs kclk coef A a ha))

theorem rejected_yes_eventually :
    ∃ onset : ℕ, ∀ N, onset ≤ N →
      recL l kclk N ((recRefuter l kclk).output (recMachine l G U P) N) = true ∧
      ¬ (recMachine l G U P).accepts N ((recRefuter l kclk).output (recMachine l G U P) N) := by
  have hlittle := (U.toUnionConstruction.runtime3 P (recL l kclk)).littleO
  obtain ⟨n₀, hone⟩ := U.soundness P (recL l kclk) (recL_inNTIME l kclk)
  obtain ⟨onset, hsep⟩ := (recRefuter l kclk).eventual (recMachine l G U P) hlittle
  refine ⟨max onset n₀, fun N hN => ?_⟩
  have hiff := (hsep N (le_of_max_le_left hN)).2
  set x := (recRefuter l kclk).output (recMachine l G U P) N
  have hrej : ¬ (recMachine l G U P).accepts N x := fun hacc => by
    have h1 : recL l kclk N x = true := hone N (le_of_max_le_right hN) x hacc
    have h2 := hiff.1 hacc
    unfold recL at h1
    rw [h1] at h2
    exact Bool.noConfusion h2
  refine ⟨?_, hrej⟩
  unfold recL
  cases hx : (recRefuter l kclk).hierarchy.timedView.accepts N x
  · exact absurd (hiff.2 hx) hrej
  · rfl

end Refuter

end NearCubicWires.WireExponent3_5.Transfer
