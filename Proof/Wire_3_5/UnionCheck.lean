import Proof.Wire_3_5.UnionSchedule
import Proof.Wire_3_5.UnionCodec

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound)
open NearCubicWires.WireExponent3_5.Shared (uMean)

section Check
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

namespace UnionGuess
variable {S : UnionSetup I} {N : ℕ} {z : BitInput N} (g : UnionGuess S z)

/-- The guess as the check reads it, at the translation `tr`. -/
def checkData (tr : List ℕ) : UnionCheckData :=
  ⟨g.mode, g.q, (S.request z g.oracle).circuit, g.pcpp, g.s, g.sign, g.atom, S.constAtom g.mode g.q,
    S.parityAtom g.mode g.q, S.gridMass g.q, tr⟩

theorem checkData_circ (tr : List ℕ) : (g.checkData tr).circ = g.circ := by
  funext x
  rcases x with _ | ⟨X, a⟩ | X <;> rfl

theorem checkData_vCall (pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2) (t : Fin 4 → g.AtomIx) :
    (g.checkData g.translation).vCall pos t = g.vCall pos t := by
  unfold UnionCheckData.vCall UnionGuess.vCall
  rw [checkData_circ]
  rfl

theorem checkData_muCall (i : Fin (2 ^ g.pcpp.clauseBits)) (t : Fin 4 → g.AtomIx) :
    (g.checkData g.translation).muCall i t = g.muCall i t := by
  unfold UnionCheckData.muCall UnionGuess.muCall
  rw [checkData_circ]
  rfl

theorem castF_wS (tr : List ℕ) (X : PcppVar g.pcpp) : castF ((g.checkData tr).wS X) = g.wS X := by
  funext y
  rcases y with _ | ⟨Y, a⟩ | Y
  · simp [castF, UnionCheckData.wS, UnionGuess.wS]
  · simp only [castF, UnionCheckData.wS, UnionGuess.wS]
    split_ifs with h1 h2 h2 <;>
      first | exact absurd h1 h2 | exact absurd h2 h1 | (push_cast; rfl)
  · simp [castF, UnionCheckData.wS, UnionGuess.wS]

theorem castF_wOne (tr : List ℕ) : castF (g.checkData tr).wOne = g.wOne := by
  funext y
  rcases y with _ | ⟨Y, a⟩ | Y <;> simp [castF, UnionCheckData.wOne, UnionGuess.wOne]

theorem castF_wE (tr : List ℕ) (X : PcppVar g.pcpp) : castF ((g.checkData tr).wE X) = g.wE X := by
  funext y
  rcases y with _ | ⟨Y, a⟩ | Y
  · simp [castF, UnionCheckData.wE, UnionGuess.wE]
  · simp [castF, UnionCheckData.wE, UnionGuess.wE]
  · simp only [castF, UnionCheckData.wE, UnionGuess.wE]
    split_ifs with h1 h2 h2 <;> first | exact absurd h1 h2 | exact absurd h2 h1 | simp

theorem polyVAt_eq (tr : List ℕ) (pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2) :
    g.polyVAt pos = ((g.checkData tr).polyVAt pos).toReal := by
  rw [UnionCheckData.polyVAt, polyVQ_toReal, castF_wS, castF_wOne, castF_wE]
  rfl

theorem polyQAt_eq (tr : List ℕ) (pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2) :
    g.polyQAt pos = ((g.checkData tr).polyQAt pos).toReal := by
  rw [UnionCheckData.polyQAt, polyQQ_toReal, castF_wS, castF_wOne]
  rfl

theorem polyMuAt_eq (tr : List ℕ) (i : Fin (2 ^ g.pcpp.clauseBits)) :
    g.polyMuAt i = ((g.checkData tr).polyMuAt i).toReal := by
  rw [UnionCheckData.polyMuAt, polyMuQ_toReal, castF_wS, castF_wS, castF_wOne]
  rfl

theorem coeffV_eq (tr : List ℕ) (pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2) (j : Fin 4) (t : Fin 4 → g.AtomIx) :
    (g.polyVAt pos).coeff j t = (((g.checkData tr).polyVAt pos).coeff j t : ℝ) := by
  rw [g.polyVAt_eq tr pos]
  exact Poly4Q.coeff_toReal _ _ _

theorem coeffQ_eq (tr : List ℕ) (pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2) (j : Fin 4) (t : Fin 4 → g.AtomIx) :
    (g.polyQAt pos).coeff j t = (((g.checkData tr).polyQAt pos).coeff j t : ℝ) := by
  rw [g.polyQAt_eq tr pos]
  exact Poly4Q.coeff_toReal _ _ _

theorem coeffMu_eq (tr : List ℕ) (i : Fin (2 ^ g.pcpp.clauseBits)) (j : Fin 4) (t : Fin 4 → g.AtomIx) :
    (g.polyMuAt i).coeff j t = (((g.checkData tr).polyMuAt i).coeff j t : ℝ) := by
  rw [g.polyMuAt_eq tr i]
  exact Poly4Q.coeff_toReal _ _ _

theorem coeffV_ne_zero (tr : List ℕ) (pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2) (j : Fin 4)
    (t : Fin 4 → g.AtomIx) : (g.polyVAt pos).coeff j t ≠ 0 ↔ ((g.checkData tr).polyVAt pos).coeff j t ≠ 0 := by
  rw [g.coeffV_eq tr pos j t]
  exact Rat.cast_ne_zero

theorem coeffQ_ne_zero (tr : List ℕ) (pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2) (j : Fin 4)
    (t : Fin 4 → g.AtomIx) : (g.polyQAt pos).coeff j t ≠ 0 ↔ ((g.checkData tr).polyQAt pos).coeff j t ≠ 0 := by
  rw [g.coeffQ_eq tr pos j t]
  exact Rat.cast_ne_zero

theorem coeffMu_ne_zero (tr : List ℕ) (i : Fin (2 ^ g.pcpp.clauseBits)) (j : Fin 4) (t : Fin 4 → g.AtomIx) :
    (g.polyMuAt i).coeff j t ≠ 0 ↔ ((g.checkData tr).polyMuAt i).coeff j t ≠ 0 := by
  rw [g.coeffMu_eq tr i j t]
  exact Rat.cast_ne_zero

variable (P : FusedPrimitive I)

/-- The rational `V̂` of the check is the machine's `V̂`. -/
theorem Vhat_eq : g.Vhat P = ((g.checkData g.translation).VhatQ P.value : ℝ) := by
  have hc : ((Fintype.card (Fin (2 ^ g.pcpp.clauseBits) × Fin 2) : ℕ) : ℝ) =
      (2 : ℝ) ^ (g.checkData g.translation).pcpp.clauseBits * 2 := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; push_cast; rfl
  unfold UnionGuess.Vhat uMean Poly4.estimate
  rw [UnionCheckData.VhatQ, UnionCheckData.combine_termsV, hc]
  push_cast
  rw [div_left_inj' (by positivity)]
  refine Finset.sum_congr rfl fun pos _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => ?_
  rw [g.coeffV_eq g.translation pos j t, g.checkData_vCall pos t]

/-- The rational `Q̂` of the check is the machine's `Q̂`. -/
theorem Qhat_eq : g.Qhat P = ((g.checkData g.translation).QhatQ P.value : ℝ) := by
  have hc : ((Fintype.card (Fin (2 ^ g.pcpp.clauseBits) × Fin 2) : ℕ) : ℝ) =
      (2 : ℝ) ^ (g.checkData g.translation).pcpp.clauseBits * 2 := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; push_cast; rfl
  unfold UnionGuess.Qhat uMean Poly4.estimate
  rw [UnionCheckData.QhatQ, UnionCheckData.combine_termsQ, hc]
  push_cast
  rw [div_left_inj' (by positivity)]
  refine Finset.sum_congr rfl fun pos _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => ?_
  rw [g.coeffQ_eq g.translation pos j t, g.checkData_vCall pos t]

/-- The rational `μ̂` of the check is the machine's `μ̂`. -/
theorem μhat_eq : g.μhat P = ((g.checkData g.translation).μhatQ P.value : ℝ) := by
  have hc : ((Fintype.card (Fin (2 ^ g.pcpp.clauseBits)) : ℕ) : ℝ) =
      (2 : ℝ) ^ (g.checkData g.translation).pcpp.clauseBits := by
    rw [Fintype.card_fin]; push_cast; rfl
  unfold UnionGuess.μhat uMean Poly4.estimate
  rw [UnionCheckData.μhatQ, UnionCheckData.combine_termsMu, hc]
  push_cast
  rw [div_left_inj' (by positivity)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => ?_
  rw [g.coeffMu_eq g.translation i j t, g.checkData_muCall i t]

end UnionGuess

/-- **The union machine's check on a parsed guess**: oracle size `≤ q^G`, the word bound `⌊N/16⌋`, then the
schedule's check (grid signs, admissible calls, `tr:thresholds` in exact rationals). -/
def unionCheck (S : UnionSetup I) {N : ℕ} (z : BitInput N) (g : UnionGuess S z) (tr : List ℕ)
    (callOk : PrimRequest → Bool) (val : PrimRequest → ℚ) : Bool :=
  decide (g.oracle.size ≤ oracleSizeBound S.G (S.pcp.nativeWidth N)) && decide (g.word.length ≤ N / 16) &&
    (g.checkData tr).check val S.params.v0 S.params.threshold callOk

variable {S : UnionSetup I} {N : ℕ} {z : BitInput N}

/-- **The check computes `UnionAccepts`** at the primitive's printed values, when `callOk` decides `I.Call` on the
scheduled requests. -/
theorem unionCheck_iff (P : FusedPrimitive I) (g : UnionGuess S z) (callOk : PrimRequest → Bool)
    (hok : ∀ r ∈ (g.checkData g.translation).schedule, callOk r = true ↔ I.Call r) :
    unionCheck S z g g.translation callOk P.value = true ↔ UnionAccepts S P z g := by
  have hV : (∀ pos j t, ((g.checkData g.translation).polyVAt pos).coeff j t ≠ 0 →
      I.Call ((g.checkData g.translation).vCall pos t)) ↔
      ∀ pos j t, (g.polyVAt pos).coeff j t ≠ 0 → I.Call (g.vCall pos t) := by
    constructor
    · intro h pos j t hc
      exact g.checkData_vCall pos t ▸ h pos j t ((g.coeffV_ne_zero _ pos j t).1 hc)
    · intro h pos j t hc
      exact (g.checkData_vCall pos t).symm ▸ h pos j t ((g.coeffV_ne_zero _ pos j t).2 hc)
  have hQ : (∀ pos j t, ((g.checkData g.translation).polyQAt pos).coeff j t ≠ 0 →
      I.Call ((g.checkData g.translation).vCall pos t)) ↔
      ∀ pos j t, (g.polyQAt pos).coeff j t ≠ 0 → I.Call (g.vCall pos t) := by
    constructor
    · intro h pos j t hc
      exact g.checkData_vCall pos t ▸ h pos j t ((g.coeffQ_ne_zero _ pos j t).1 hc)
    · intro h pos j t hc
      exact (g.checkData_vCall pos t).symm ▸ h pos j t ((g.coeffQ_ne_zero _ pos j t).2 hc)
  have hM : (∀ i j t, ((g.checkData g.translation).polyMuAt i).coeff j t ≠ 0 →
      I.Call ((g.checkData g.translation).muCall i t)) ↔
      ∀ i j t, (g.polyMuAt i).coeff j t ≠ 0 → I.Call (g.muCall i t) := by
    constructor
    · intro h i j t hc
      exact g.checkData_muCall i t ▸ h i j t ((g.coeffMu_ne_zero _ i j t).1 hc)
    · intro h i j t hc
      exact (g.checkData_muCall i t).symm ▸ h i j t ((g.coeffMu_ne_zero _ i j t).2 hc)
  have hcalls : (g.checkData g.translation).schedule.all callOk = true ↔
      ((∀ pos j t, (g.polyVAt pos).coeff j t ≠ 0 → I.Call (g.vCall pos t)) ∧
        (∀ pos j t, (g.polyQAt pos).coeff j t ≠ 0 → I.Call (g.vCall pos t)) ∧
        (∀ i j t, (g.polyMuAt i).coeff j t ≠ 0 → I.Call (g.muCall i t))) := by
    rw [List.all_eq_true, ← hV, ← hQ, ← hM, ← UnionCheckData.forall_schedule_iff]
    exact forall₂_congr fun r hr => hok r hr
  have hsigns : (g.checkData g.translation).signsOk = true ↔ ∀ X a, g.sign X a ∈ ({-1, 0, 1} : Finset ℤ) := by
    unfold UnionCheckData.signsOk
    exact decide_eq_true_iff
  have e1 : (g.checkData g.translation).VhatQ P.value ≤ 2 * S.params.v0 ↔ g.Vhat P ≤ 2 * (S.params.v0 : ℝ) := by
    rw [g.Vhat_eq P]; constructor <;> intro h <;> exact_mod_cast h
  have e2 : (g.checkData g.translation).QhatQ P.value ≤ 1 + S.params.v0 ↔ g.Qhat P ≤ 1 + (S.params.v0 : ℝ) := by
    rw [g.Qhat_eq P]; constructor <;> intro h <;> exact_mod_cast h
  have e3 : S.params.threshold ≤ (g.checkData g.translation).μhatQ P.value ↔
      (S.params.threshold : ℝ) ≤ g.μhat P := by
    rw [g.μhat_eq P]; constructor <;> intro h <;> exact_mod_cast h
  unfold unionCheck UnionCheckData.check
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff, hcalls, hsigns,
    e1, e2, e3]
  constructor
  · rintro ⟨⟨hsize, hword⟩, ⟨⟨⟨hsg, hcV, hcQ, hcM⟩, hv⟩, hq⟩, hm⟩
    exact ⟨hsize, hsg, hword, hcV, hcQ, hcM, hv, hq, hm⟩
  · rintro ⟨hsize, hsg, hword, hcV, hcQ, hcM, hv, hq, hm⟩
    exact ⟨⟨hsize, hword⟩, ⟨⟨⟨hsg, hcV, hcQ, hcM⟩, hv⟩, hq⟩, hm⟩

/-- **The union machine's run on a witness**: decode it, then check. -/
def unionRun (S : UnionSetup I) {N : ℕ} (z : BitInput N) (tr : UnionGuess S z → List ℕ) (callOk : PrimRequest → Bool)
    (val : PrimRequest → ℚ) (w : List Bool) : Bool :=
  match decodeGuess S z w with
  | none => false
  | some g => unionCheck S z g (tr g) callOk val

/-- **Soundness direction** (`SoundFor`): an accepting run yields an accepting guess. -/
theorem unionRun_sound (P : FusedPrimitive I) (callOk : PrimRequest → Bool)
    (hok : ∀ g : UnionGuess S z, ∀ r ∈ (g.checkData g.translation).schedule, callOk r = true ↔ I.Call r)
    (w : List Bool) (h : unionRun S z UnionGuess.translation callOk P.value w = true) :
    ∃ g : UnionGuess S z, UnionAccepts S P z g := by
  unfold unionRun at h
  split at h
  · exact absurd h Bool.false_ne_true
  · exact ⟨_, (unionCheck_iff P _ callOk (hok _)).1 h⟩

/-- **Completeness direction** (`CompleteFor`): an accepting guess is accepted on a witness of every length
`W ≥ ⌊N/16⌋`. -/
theorem unionRun_complete (P : FusedPrimitive I) (callOk : PrimRequest → Bool) (g : UnionGuess S z)
    (hok : ∀ r ∈ (g.checkData g.translation).schedule, callOk r = true ↔ I.Call r) (hg : UnionAccepts S P z g)
    (W : ℕ) (hW : N / 16 ≤ W) :
    ∃ w : List Bool, w.length = W ∧ unionRun S z UnionGuess.translation callOk P.value w = true := by
  have hlen : g.word.length ≤ W := hg.2.2.1.trans hW
  refine ⟨encodeGuess g ++ List.replicate (W - g.word.length) false, ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate, encodeGuess]
    omega
  · unfold unionRun
    rw [decodeGuess_encodeGuess]
    exact (unionCheck_iff P g callOk hok).2 hg

/-- **The schedule's length is polynomial**: at most `24·K·(1 + 2K(s+1))⁴` for `K = c·(size(H)+1)^d`. -/
theorem length_schedule_le (g : UnionGuess S z) (tr : List ℕ) :
    (g.checkData tr).schedule.length ≤
      24 * (S.pcppAlg.coefficient * ((S.request z g.oracle).circuit.size + 1) ^ S.pcppAlg.degree) *
        (1 + 2 * (S.pcppAlg.coefficient * ((S.request z g.oracle).circuit.size + 1) ^ S.pcppAlg.degree) *
          (g.s + 1)) ^ 4 := by
  set K := S.pcppAlg.coefficient * ((S.request z g.oracle).circuit.size + 1) ^ S.pcppAlg.degree with hK
  have hM : 2 ^ (g.checkData tr).pcpp.clauseBits ≤ K := S.pcppAlg.clauseCountBound (S.request z g.oracle)
  have hsys : (g.checkData tr).pcpp.systematicBits ≤ K := by
    refine (S.pcppAlg.systematicBound (S.request z g.oracle)).trans (Nat.mul_le_mul_left _ ?_)
    exact Nat.pow_le_pow_left (by have := (S.request z g.oracle).sizeLarge; omega) _
  have haux : (g.checkData tr).pcpp.auxiliaryBits ≤ K := S.pcppAlg.auxiliaryBound (S.request z g.oracle)
  have hA : (g.checkData tr).atomCount ≤ 1 + 2 * K * (g.s + 1) := by
    unfold UnionCheckData.atomCount UnionCheckData.nvars
    have hs : (g.checkData tr).s = g.s := rfl
    rw [hs]
    have hnv : (g.checkData tr).pcpp.systematicBits + (g.checkData tr).pcpp.auxiliaryBits ≤ 2 * K := by omega
    nlinarith [Nat.mul_le_mul_right (g.s + 1) hnv]
  calc (g.checkData tr).schedule.length
      ≤ 3 * (2 ^ (g.checkData tr).pcpp.clauseBits * 2) * (4 * (g.checkData tr).atomCount ^ 4) :=
        (g.checkData tr).length_schedule
    _ ≤ 3 * (K * 2) * (4 * (1 + 2 * K * (g.s + 1)) ^ 4) := by gcongr
    _ = 24 * K * (1 + 2 * K * (g.s + 1)) ^ 4 := by ring

end Check

end NearCubicWires.WireExponent3_5.Transfer
