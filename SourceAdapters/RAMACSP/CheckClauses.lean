import SourceAdapters.RAMACSP.CheckRoutingDock
import SourceAdapters.ACSP.AffineDegree
import SourceAdapters.Joins.AffineConstraint
import SourceAdapters.Routing.LayoutBank
import SourceAdapters.Joins.RAMEventTrace

/-!
# Assembling the affine constraint reduction

The separate mathematical, representation and machine certificates of Step 1
of `thm:short-pcp-ours` assemble the single direct-I instance of `def:acsp`.
Only acceptance requires `RunsWithin`; validity and canonical masks hold under
`2 ≤ n ≤ t`. The generator remains total on all clock requests. The support
weight bound is a direct certificate, and reduced circuit constants are kept
separate from frame data until full canonical syntax is assembled.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP

open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ACSP NearCubicGates.Adapters.Joins
open NearCubicGates.Adapters
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairSource NearCubicWires.LocalBitMultitape
open Polynomial

/-! ## Budget weakening of a word function -/

/-- Extra fuel does not change a finished run. (Copied from `Proof/Gates/WorkerArith/WeakWorkerA.lean`,
`runFrom_mono`.) -/
theorem runFrom_mono {t s : ℕ} (M : Machine t s) :
    ∀ (f f' : ℕ) (c : Configuration t s) (r : ExecutionReceipt t s), runFrom M f c = some r → f ≤ f' →
      runFrom M f' c = some r
  | 0, f', c, r, h, _ => by
    simp only [runFrom] at h
    split at h
    · next hh =>
      cases f' with
      | zero => simp [runFrom, hh] at h ⊢; exact h
      | succ f' => simp [runFrom, hh] at h ⊢; exact h
    · cases h
  | f + 1, f', c, r, h, hle => by
    obtain ⟨f'', rfl⟩ : ∃ f'', f' = f'' + 1 := ⟨f' - 1, by omega⟩
    simp only [runFrom] at h ⊢
    split at h
    · next hh => rw [if_pos hh]; exact h
    · next hh =>
      rw [if_neg hh]
      split at h
      · cases h
      · next next' hs =>
        split at h
        · cases h
        · next suf hsuf =>
          rw [runFrom_mono M f f'' next' suf hsuf (by omega)]
          exact h

/-- A word function within a budget is one within any larger budget. -/
def wordFunctionRelax {Req : Type} {inp out : Req → List Bool} {b b' : Req → ℕ} (hb : ∀ r, b r ≤ b' r)
    (F : OrdinaryWordFunction Req inp out b) : OrdinaryWordFunction Req inp out b' where
  program := F.program
  realizes r := by
    obtain ⟨rc, h1, h2⟩ := F.realizes r
    exact ⟨rc, runFrom_mono _ _ _ _ _ h1 (hb r), h2⟩

/-- `K·a^e ≤ K'·a^{e'}` for `a ≥ 1`, `K ≤ K'`, `e ≤ e'`. -/
theorem mul_pow_mono {a K K' e e' : ℕ} (ha : 1 ≤ a) (hK : K ≤ K') (he : e ≤ e') : K * a ^ e ≤ K' * a ^ e' :=
  Nat.mul_le_mul hK (Nat.pow_le_pow_right ha he)

/-! ## The machine `M_n` and the assembly conditions -/

variable (V : Verifier)

/-- P02's `M_n` at the clock parameters (`w = w_n`, `T = 2^τ`; `app:event-trace` Setting). -/
abbrev ownRam (r : ClockRequest) : Ram :=
  mnRam V (wordWidth (clockConst V) r.2) r.1.1 r.2 (2 ^ timeExp (clockConst V) r.2) (codeLen_le_two_pow_wordW V r.2)

variable (irrPoly : ℕ → (ZMod 2)[X]) (cons : ClockRequest → List CodeGate)

/-- **the embedding theorem** (`thm:embedding` Full embedding equivalence: the global affine constraint
instance accepts `x̄` iff `ET(M, τ, x̄)` is satisfiable; the input-acceptance clause of `def:acsp`; the interpolation argument in `thm:embedding`). Over the instance field. -/
def EmbeddingEquivalence : Prop :=
  ∀ r : ClockRequest, 2 ≤ r.1.1 → r.1.1 ≤ r.2 → ∀ [Fact (Irreducible (ownIrr V irrPoly cons r))],
    (RAMTrace.Satisfiable (Field2 (ownIrr V irrPoly cons r)) (ownRam V r) RAMTrace.mnKind
        (timeExp (clockConst V) r.2) (padInput (clockConst V) r.2 r.1.2) ↔
      (ownInst V irrPoly cons r).Accepts (ownXbar V r))

/-- **the degree constraint** `4·wdeg P ≤ 2^f` (`lem:acsp-degree`, the degree argument of `lem:acsp-degree`, `lem:acsp-degree` Choice of `f`). -/
def DegreeBound : Prop :=
  ∀ r : ClockRequest, 2 ≤ r.1.1 → r.1.1 ≤ r.2 → ∃ dB : ℕ, (ownInst V irrPoly cons r).HasDegreeBound dB ∧ 4 * dB ≤ 2 ^ (ownInst V irrPoly cons r).f

/-- **Reduced constants of the constraint circuit.** The serialized field constants must be
`f`-bit masks, including the bit constants `0, 1`. This is the field-word encoding used by the
construction of `lem:generator`. -/
def ConstraintConstantsReduced : Prop :=
  ∀ r : ClockRequest, 2 ≤ r.1.1 → r.1.1 ≤ r.2 → ∀ g ∈ (ownInst V irrPoly cons r).cons, ∀ v, g = CodeGate.const v →
    v < 2 ^ (ownInst V irrPoly cons r).f

/-- **Parameter size** (`lem:generator`): `|word(inst)| ≤ K·(logScale t + 1)^e`. -/
def ParameterSize : Prop :=
  ∃ K e : ℕ, ∀ r : ClockRequest, 2 ≤ r.1.1 → r.1.1 ≤ r.2 →
    (ownInst V irrPoly cons r).word.length ≤ K * (logScale r.2 + 1) ^ e

/-- **The generator** (`lem:generator`): an ordinary machine on `frame x ++ frame (bits t)` with output
`frame (frame x̄ ++ word(inst))` within `K·(n + |bits t| + 1)^e`. -/
def GeneratorMachine : Prop :=
  ∃ K e : ℕ, Nonempty (OrdinaryWordFunction ClockRequest ClockRequest.word
    (fun r => RepairSource.frame (RepairSource.frame (ownXbar V r) ++ (ownInst V irrPoly cons r).word))
    (fun r => K * (r.1.1 + natBitLength r.2 + 1) ^ e))

/-- Canonical frame masks, without a claim about the parameterized circuit. -/
def FrameMasks (r : ClockRequest) : Prop :=
  let c := ownInst V irrPoly cons r
  c.irr.testBit c.f = true ∧ c.irr < 2 ^ (c.f + 1) ∧
  (∀ a ∈ c.hBasis, a < 2 ^ c.f) ∧ c.hOffset < 2 ^ c.f ∧
  (∀ p ∈ c.nbr, p.1 < 2 ^ c.f ∧ p.2 < 2 ^ c.f) ∧
  (∀ a ∈ c.iBasis, a < 2 ^ c.f) ∧ c.iOffset < 2 ^ c.f

/-- Frame masks, modulus, H and the one selected input subspace. -/
def FrameSyntax : Prop :=
  ∀ r : ClockRequest, 2 ≤ r.1.1 → r.1.1 ≤ r.2 →
    FrameMasks V irrPoly cons r ∧
    Irreducible (ownInst V irrPoly cons r).irrPoly ∧
    (ownInst V irrPoly cons r).irrPoly.natDegree = (ownInst V irrPoly cons r).f ∧
    AffineIndependent (ownInst V irrPoly cons r).irrPoly (ownInst V irrPoly cons r).mH
      (ownInst V irrPoly cons r).hBasisPoly (WireExponent3_5.GF.toPoly (ownInst V irrPoly cons r).hOffset) ∧
    (AffineIndependent (ownInst V irrPoly cons r).irrPoly (ownInst V irrPoly cons r).m
      (ownInst V irrPoly cons r).iBasisPoly (WireExponent3_5.GF.toPoly (ownInst V irrPoly cons r).iOffset) ∧
      ∀ c, ∃ c', (ownInst V irrPoly cons r).iEltOf c = (ownInst V irrPoly cons r).hElt c')

/-- Field, bank and padded-input resource bounds. -/
def FrameBounds : Prop :=
  ∃ K e : ℕ, ∀ r : ClockRequest, 2 ≤ r.1.1 → r.1.1 ≤ r.2 →
    (2 ^ fieldExp V r.2 ≤ K * r.2 * logScale r.2 ^ e ∧ fieldExp V r.2 ≤ K * (logScale r.2 + 1) ∧
      (ownInst V irrPoly cons r).cN ≤ K * logScale r.2 ∧ (ownInst V irrPoly cons r).cN ≤ K * fieldExp V r.2) ∧
    (((ownXbar V r).length = 2 ^ (ownInst V irrPoly cons r).m ∧
        1 ≤ (ownInst V irrPoly cons r).m ∧ (ownInst V irrPoly cons r).m < (ownInst V irrPoly cons r).mH) ∧
      (ownXbar V r).length ≤ K * (r.1.1 + logScale r.2))

/-- The nonempty neighbor bank has nonzero slopes. -/
def FrameNeighbors : Prop :=
  ∀ r : ClockRequest, 2 ≤ r.1.1 → r.1.1 ≤ r.2 →
    1 ≤ (ownInst V irrPoly cons r).cN ∧
      ∀ p ∈ (ownInst V irrPoly cons r).nbr, (ownInst V irrPoly cons r).elt p.1 ≠ 0

/-! ## Proved clauses -/

theorem ownInst_hBasis_length (r : ClockRequest) :
    (ownInst V irrPoly cons r).hBasis.length = domExp V r.2 := by
  simp [ownInst]

/-- **C5 [J2, M1]** (`lem:acsp-degree`: `f = mH + ⌈log₂(4(mH+4))⌉ ≥ mH + 2`). -/
theorem ownInst_f (r : ClockRequest) : (ownInst V irrPoly cons r).f = fieldExp V r.2 := rfl

theorem clause_field (r : ClockRequest) :
    (ownInst V irrPoly cons r).hBasis.length + 2 ≤ (ownInst V irrPoly cons r).f ∧
      (ownInst V irrPoly cons r).hBasis.length < (ownInst V irrPoly cons r).f := by
  rw [ownInst_hBasis_length, ownInst_f]
  have := domExp_add_two_le_fieldExp V r.2
  exact ⟨this, by omega⟩

/-- Every neighbor pair contains canonical masks. -/
theorem clause_nbr_consts (r : ClockRequest) :
    ∀ p ∈ (ownInst V irrPoly cons r).nbr,
      p.1 < 2 ^ (ownInst V irrPoly cons r).f ∧ p.2 < 2 ^ (ownInst V irrPoly cons r).f := by
  intro p hp
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
  have hmf := domExp_add_two_le_fieldExp V r.2
  refine ⟨Nat.one_lt_two_pow (by change fieldExp V r.2 ≠ 0; omega), ?_⟩
  exact (Routing.LayoutFacts.globalBank_lt (ownLayout V r.2) b hb).trans_le
    (Nat.pow_le_pow_right (by norm_num) (by change domExp V r.2 ≤ fieldExp V r.2; omega))

/-- The support-weight certificate implies the one-way bound on compositions. -/
theorem clause_degree (r : ClockRequest)
    (hD : ∃ dB : ℕ, (ownInst V irrPoly cons r).HasDegreeBound dB ∧
      4 * dB ≤ 2 ^ (ownInst V irrPoly cons r).f) :
    ∃ dB : ℕ, dB * 4 ≤ 2 ^ (ownInst V irrPoly cons r).f ∧
      ∀ A : (ownInst V irrPoly cons r).Fld[X],
        A.degree < ((2 ^ (ownInst V irrPoly cons r).mH : ℕ) : WithBot ℕ) →
          ((ownInst V irrPoly cons r).composed A).natDegree ≤ dB := by
  obtain ⟨dB, hB, h4⟩ := hD
  exact ⟨dB, by omega, fun A hA => ACSP.Affine.Instance.composed_natDegree_le _ hB A hA⟩

/-- The frame and the reduced circuit constants form the complete canonical word. -/
theorem frame_wellFormed (r : ClockRequest) (hM : FrameMasks V irrPoly cons r)
    (hK : ∀ g ∈ (ownInst V irrPoly cons r).cons, ∀ v, g = CodeGate.const v → v < 2 ^ (ownInst V irrPoly cons r).f) :
    (ownInst V irrPoly cons r).WellFormed :=
  ⟨hM.1, hM.2.1, hM.2.2.1, hM.2.2.2.1, hM.2.2.2.2.1, hK, hM.2.2.2.2.2⟩

/-- The separate concrete certificates assemble the exact direct-I reduction. -/
theorem affineConstraint_of_frontier (hI : Published.Shoup.IrreducibleChoice irrPoly)
    (hET : Joins.RAMEventTrace)
    (hE : EmbeddingEquivalence V irrPoly cons) (hD : DegreeBound V irrPoly cons)
    (hK : ConstraintConstantsReduced V irrPoly cons) (hS : ParameterSize V irrPoly cons)
    (hG : GeneratorMachine V irrPoly cons) (hF1 : FrameSyntax V irrPoly cons) (hF2 : FrameBounds V irrPoly cons)
    (hF3 : FrameNeighbors V irrPoly cons) : Joins.AffineConstraintReduction V := by
  obtain ⟨K1, e1, hB⟩ := hF2
  obtain ⟨K2, e2, hW⟩ := hS
  obtain ⟨K3, e3, ⟨gen⟩⟩ := hG
  refine ⟨ownInst V irrPoly cons, ownXbar V, K1 + K2 + K3, e1 + e2 + e3, ?_, ?_⟩
  · intro r hn hnt
    obtain ⟨hM, hirr, hdeg, hH, hInput⟩ := hF1 r hn hnt
    obtain ⟨⟨h1, h2, _, h4⟩, ⟨hLen, hPositive, hStrict⟩, hX⟩ := hB r hn hnt
    have hK1 : K1 ≤ K1 + K2 + K3 := by omega
    refine ⟨?_, ⟨⟨hirr, hdeg⟩, hH, hF3 r hn hnt, hInput, hD r hn hnt⟩,
      frame_wellFormed V irrPoly cons r hM (hK r hn hnt),
      ⟨_, ownXbar_padding V r⟩, hLen, hPositive, hStrict, (clause_field V irrPoly cons r).1,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro hrun
      haveI := ownIrr_fact V irrPoly cons r hI
      exact (hET.2 (Field2 (ownIrr V irrPoly cons r)) V (clockConst V) le_rfl r
        (codeLen_le_two_pow_wordW V r.2) hn hnt hrun).trans (hE r hn hnt)
    · exact h1.trans (mul_pow_mono (logScale_facts r.2).1 (Nat.mul_le_mul_right _ hK1) (by omega))
    · exact h2.trans (Nat.mul_le_mul_right _ hK1)
    · exact h4.trans (Nat.mul_le_mul_right _ hK1)
    · exact hX.trans (Nat.mul_le_mul_right _ hK1)
    · exact (hW r hn hnt).trans (mul_pow_mono (by omega) (by omega) (by omega))
  · exact ⟨wordFunctionRelax (fun r => mul_pow_mono (by omega) (by omega) (by omega)) gen⟩

end NearCubicGates.Adapters.RAMACSP
