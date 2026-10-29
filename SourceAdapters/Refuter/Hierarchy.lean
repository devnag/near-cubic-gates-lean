import SourceAdapters.Refuter.HierarchyMachine
import SourceAdapters.Refuter.Witnesses
import SourceAdapters.Refuter.UniformCap

/-!
# The hierarchy language obeys the recurrence (input 7, the join `HierarchyRecurrence`)

`cor:framed-refuter`: for every promised `M`, at all sufficiently large `N`,
"`L^fr_T(x_i) = [V_M^fr(x_1,T(N),w_i)=0] · (M(x_{i+1}) if i<s, 1 if i=s)`", with
`L^fr_T` the language of a verifier with "time bound `c(T(N)+1)`, and exactly `c(T(N)+1)` witness bits"
. `hierarchyOf` is that verifier (`hverifier`, coefficient `hcoef C`); `hierarchyRecurrence`
proves the join `HierarchyRecurrence` (`Assembly.lean`) for it at every clock with `N ≤ T(N)`.

Soundness (proof of `lem:multitape-refuter`, "every verified verdict is genuine"): an accepting branch certifies, by
`trace_genuine`, a rejecting halt of `M` on `x_1, w_i` and, when `i<s`, an accepting halt on `x_{i+1}` with the
guessed `v`. Completeness: the guess with `r = t_M(N)+2` (`weak_trace_useful`), encoded
by `encCheck`, runs within the cap `1024(T(N)+1)` at large `N` (`useful_branch_fits_cap` with `c_0 = 1022`) and
fits in the `c(T(N)+1)` witness bits.
-/

namespace NearCubicGates.Adapters.Refuter.Clock

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Adapters.Refuter NearCubicGates.Adapters.Refuter.Mach
open NearCubicGates.Close.CheckedPCPP (coldBank)
open NearCubicGates.Adapters.Joins
open NearCubicWires.Bindings.CLW20Theorem113

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## The hierarchy -/

/-- The coefficient `c` of `cor:framed-refuter`; proof of `cor:framed-refuter`. -/
def hcoef (C : ℕ) : ℕ := 2002000 + 100 * C

theorem steps_le (T : ℕ → ℕ) (hT : ∀ n, n ≤ T n) (C n : ℕ) :
    prepBound C n (T n) + 1 + (clockLen (T n) + 1) ≤ hcoef C * (T n + 1) := by
  have := hT n
  unfold prepBound clockLen hcoef
  nlinarith

/-- **The hierarchy verifier** of `cor:framed-refuter` (time bound and witness length `c(T(N)+1)`). -/
noncomputable def hierarchyOf (hcr : CappedMachineRun) (T : ℕ → ℕ) (hT : ∀ n, n ≤ T n) (C : ℕ)
    (wf : RepairOrdinary.WordFunction ℕ (fun n => List.replicate n true) (fun n => (T n).bits) (fun n => C * (T n + 1))) :
    OrdinaryHierarchy T where
  verifier := hverifier hcr wf.program
  coefficient := hcoef C
  coefficientPositive := by unfold hcoef; omega
  halts := fun n x w => by
    obtain ⟨rH, hrun, _⟩ := hverifier_run hcr T C wf (List.ofFn x) (List.ofFn w)
    simp only [List.length_ofFn] at hrun
    have := runFrom_mono _ _ _ rH hrun (hcoef C * (T n + 1) - (prepBound C n (T n) + 1 + (clockLen (T n) + 1)))
    rw [Nat.add_sub_cancel' (steps_le T hT C n)] at this
    exact ⟨rH, this⟩

/-- The language of the hierarchy: some witness of `c(T(N)+1)` bits makes the body accept within the clock. -/
theorem hierarchy_lang (hcr : CappedMachineRun) (T : ℕ → ℕ) (hT : ∀ n, n ≤ T n) (C : ℕ)
    (wf : RepairOrdinary.WordFunction ℕ (fun n => List.replicate n true) (fun n => (T n).bits) (fun n => C * (T n + 1)))
    (N : ℕ) (x : BitInput N) :
    hierarchyLanguage (hierarchyOf hcr T hT C wf) N x = true ↔
      ∃ w : BitInput (hcoef C * (T N + 1)), BodyAcc (clockLen (T N)) (List.ofFn x) (List.ofFn w) := by
  unfold hierarchyLanguage
  simp only [decide_eq_true_eq, Verifier.language, OrdinaryHierarchy.time, hierarchyOf]
  apply exists_congr; intro w
  obtain ⟨rH, hrun, hacc⟩ := hverifier_run hcr T C wf (List.ofFn x) (List.ofFn w)
  simp only [List.length_ofFn] at hrun hacc
  rw [← hacc]
  constructor
  · rintro ⟨f, r, hr, ha⟩
    rw [runFrom_unique _ _ _ _ _ _ hr hrun] at ha; exact ha
  · intro ha; exact ⟨_, rH, hrun, ha⟩

/-! ## One record: the body's verdict -/

/-- An accepting body run within the clock certifies `BodyCond` (proof of `lem:multitape-refuter`). -/
theorem bodyAcc_sound (M : OrdinaryWeakMachine) (N i : ℕ) (w : List Bool) (cap : ℕ)
    (hv : machineIndex M + 2 + N / 16 ≤ N) (hg1 : 1 ≤ N / 16) (hi : i < 2 ^ (N / 16))
    (h : BodyAcc cap (List.ofFn (record M N i)) w) : BodyCond M N i w := by
  obtain ⟨τ, cB, eB, hALL, _⟩ := body_spec (bodyCap M N w) M N i w hv hg1 hi le_rfl
  obtain ⟨rB0, hrB0, hctl⟩ := bodyFull_run (List.ofFn (record M N i)) w τ cB eB
  obtain ⟨rB, hrB, hacc⟩ := h
  have he := runFrom_unique _ _ _ _ _ _ hrB hrB0
  subst he
  rw [hacc] at hctl
  apply hALL.mp
  intro hz
  rw [if_neg (show ¬(τ.val rALL ≠ 0) from fun h => h hz)] at hctl
  omega

/-- A certified `BodyCond` within the clock is an accepting body run (proof of `cor:framed-refuter`). -/
theorem bodyAcc_complete (M : OrdinaryWeakMachine) (N i : ℕ) (w : List Bool) (cap : ℕ)
    (hv : machineIndex M + 2 + N / 16 ≤ N) (hg1 : 1 ≤ N / 16) (hi : i < 2 ^ (N / 16))
    (hc : BodyCond M N i w) (hcost : bodyCost M N w + 2 ≤ cap) : BodyAcc cap (List.ofFn (record M N i)) w := by
  obtain ⟨τ, cB, eB, hALL, hcB⟩ := body_spec (bodyCap M N w) M N i w hv hg1 hi le_rfl
  obtain ⟨rB0, hrB0, hctl⟩ := bodyFull_run (List.ofFn (record M N i)) w τ cB eB
  refine ⟨rB0, ?_, ?_⟩
  · have := runFrom_mono _ _ _ rB0 hrB0 (cap - (cB + 1 + 1))
    rw [show cB + 1 + 1 + (cap - (cB + 1 + 1)) = cap by omega] at this
    exact this
  · rw [hctl, if_pos (hALL.mpr hc)]

/-! ## One record: the recurrence's right side -/

/-- **Soundness at one record** (proof of `lem:multitape-refuter`; proof of `cor:framed-refuter`). -/
theorem bodyCond_rhs (T : ℕ → ℕ) (M : OrdinaryWeakMachine) (N i : ℕ) (w : List Bool)
    (hc : BodyCond M N i w) :
    (!hitData M T N i && if i + 1 < 2 ^ (N / 16) then memberData M N (i + 1) else true) = true := by
  obtain ⟨⟨hA, hAacc⟩, hB⟩ := hc
  have hhit : hitData M T N i = false := by
    unfold hitData
    simp only [decide_eq_false_iff_not]
    rintro ⟨r', hr', hacc'⟩
    obtain ⟨rcpt, hrun, hctl⟩ := trace_genuine M.verifier _ _ _ _ hA
    have := runFrom_unique _ _ _ _ _ _ hrun hr'
    subst this
    rw [hctl, hAacc] at hacc'
    cases hacc'
  rw [hhit]
  simp only [Bool.not_false, Bool.true_and]
  split_ifs with hlt
  · obtain ⟨hBc, hBacc⟩ := hB hlt
    obtain ⟨rcpt, hrun, hctl⟩ := trace_genuine M.verifier _ _ _ _ hBc
    unfold memberData machineValue
    simp only [decide_eq_true_eq]
    have hlen : (guessV M N w).length = N / 16 := by simp [guessV, gbits]
    refine ⟨fun j => (guessV M N w)[j.val]'(by rw [hlen]; exact j.isLt), rcpt.steps, rcpt, ?_, ?_⟩
    · have hv : List.ofFn (fun j : Fin (N / 16) => (guessV M N w)[j.val]'(by rw [hlen]; exact j.isLt)) = guessV M N w :=
        List.ext_getElem (by simp [hlen]) (fun j h1 h2 => by simp)
      rw [hv]
      exact runFrom_exact _ _ _ _ hrun
    · rw [hctl]; exact hBacc
  · rfl

/-! ## The useful guess -/

theorem checkerCost_mono (v : RepairOrdinary.Verifier) {r r' n n' : ℕ} (hr : r ≤ r') (hn : n ≤ n') :
    checkerCost v r n ≤ checkerCost v r' n' := by
  unfold checkerCost passesCost passCost
  gcongr

/-- `checkerCost v (t+2) t ≤ K_v (t+1)`: the useful check costs `b_M(t_M+1)`. -/
theorem checkerCost_lin (v : RepairOrdinary.Verifier) (t : ℕ) :
    checkerCost v (t + 2) t ≤ checkerCost v 3 1 * (t + 1) := by
  unfold checkerCost passesCost passCost
  generalize stepCost v = S
  generalize (VerifierEncoding.code v).length = L
  generalize v.tapeCount = c
  nlinarith [Nat.zero_le (c * t * S), Nat.zero_le (c * S), Nat.zero_le (c * L), Nat.zero_le (c * t * L),
    Nat.zero_le (c * t), Nat.zero_le (t * S), Nat.zero_le (c * c), Nat.zero_le (t * c * c)]

/-- The witness of the useful branch: first trace, the guessed `v`, second trace, padding. -/
def usefulW (t : ℕ) (r : ℕ) (dsA dsB : List (Fin t → Bool)) (vB : List Bool) (K : ℕ) : List Bool :=
  encCheck r dsA ++ (vB ++ (encCheck r dsB ++
    List.replicate (K - ((encCheck r dsA).length + vB.length + (encCheck r dsB).length)) false))

theorem usefulW_length (t r : ℕ) (dsA dsB : List (Fin t → Bool)) (vB : List Bool) (K : ℕ)
    (h : (encCheck r dsA).length + vB.length + (encCheck r dsB).length ≤ K) : (usefulW t r dsA dsB vB K).length = K := by
  simp only [usefulW, List.length_append, List.length_replicate]; omega

/-- The useful witness passes the checks the body makes (proof of `lem:multitape-refuter`). -/
theorem usefulW_cond (M : OrdinaryWeakMachine) (N i : ℕ) (r : ℕ)
    (dsA dsB : List (Fin M.verifier.tapeCount → Bool)) (vB : List Bool) (K : ℕ) (hvB : vB.length = N / 16)
    (hA : TraceChecks M.verifier.machine r
      (M.verifier.inputTapes (List.ofFn (record M N 0)) (List.ofFn (unrank (N / 16) i)))
      (traceOfD M.verifier.machine M.verifier.machine.start dsA) ∧
      M.verifier.accepting (controlAfter M.verifier.machine.start
        (traceOfD M.verifier.machine M.verifier.machine.start dsA)) = false)
    (hB : i + 1 < 2 ^ (N / 16) → TraceChecks M.verifier.machine r
      (M.verifier.inputTapes (List.ofFn (record M N (i + 1))) vB)
      (traceOfD M.verifier.machine M.verifier.machine.start dsB) ∧
      M.verifier.accepting (controlAfter M.verifier.machine.start
        (traceOfD M.verifier.machine M.verifier.machine.start dsB)) = true) :
    BodyCond M N i (usefulW M.verifier.tapeCount r dsA dsB vB K) := by
  set w := usefulW M.verifier.tapeCount r dsA dsB vB K with hw
  obtain ⟨a1, a2, a3⟩ := chk_encode [] (vB ++ (encCheck r dsB ++
    List.replicate (K - ((encCheck r dsA).length + vB.length + (encCheck r dsB).length)) false)) r dsA
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at a1 a2 a3
  have a1' : chkR0 w 0 = r := a1
  have a2' : chkDs w M.verifier.tapeCount 0 = dsA := a2
  have a3' : chkEnd w M.verifier.tapeCount 0 = (encCheck r dsA).length := a3
  have hw' : w = (encCheck r dsA ++ vB) ++ (encCheck r dsB ++
      List.replicate (K - ((encCheck r dsA).length + vB.length + (encCheck r dsB).length)) false) := by
    simp [w, usefulW]
  obtain ⟨b1, b2, _⟩ := chk_encode (encCheck r dsA ++ vB) (List.replicate
    (K - ((encCheck r dsA).length + vB.length + (encCheck r dsB).length)) false) r dsB
  rw [← hw'] at b1 b2
  have hv : guessV M N w = vB := by
    unfold guessV
    rw [a3', ← hvB]
    have := gbits_encode (encCheck r dsA) vB (encCheck r dsB ++
      List.replicate (K - ((encCheck r dsA).length + vB.length + (encCheck r dsB).length)) false)
    simpa [w, usefulW] using this
  have hs : startB M N w = (encCheck r dsA ++ vB).length := by
    unfold startB; rw [a3']; simp [hvB]
  refine ⟨?_, fun hlt => ?_⟩
  · unfold ChecksA
    rw [a1', a2']
    exact hA
  · unfold ChecksB
    rw [hv, hs, b1, b2]
    exact hB hlt

/-- What the body parses from the useful witness. -/
theorem usefulW_parse (M : OrdinaryWeakMachine) (N r : ℕ)
    (dsA dsB : List (Fin M.verifier.tapeCount → Bool)) (vB : List Bool) (K : ℕ) (hvB : vB.length = N / 16) :
    chkR0 (usefulW M.verifier.tapeCount r dsA dsB vB K) 0 = r ∧
    chkDs (usefulW M.verifier.tapeCount r dsA dsB vB K) M.verifier.tapeCount 0 = dsA ∧
    chkR0 (usefulW M.verifier.tapeCount r dsA dsB vB K) (startB M N (usefulW M.verifier.tapeCount r dsA dsB vB K)) = r ∧
    chkDs (usefulW M.verifier.tapeCount r dsA dsB vB K) M.verifier.tapeCount
      (startB M N (usefulW M.verifier.tapeCount r dsA dsB vB K)) = dsB := by
  set w := usefulW M.verifier.tapeCount r dsA dsB vB K with hw
  obtain ⟨a1, a2, a3⟩ := chk_encode [] (vB ++ (encCheck r dsB ++
    List.replicate (K - ((encCheck r dsA).length + vB.length + (encCheck r dsB).length)) false)) r dsA
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at a1 a2 a3
  have a3' : chkEnd w M.verifier.tapeCount 0 = (encCheck r dsA).length := a3
  have hw' : w = (encCheck r dsA ++ vB) ++ (encCheck r dsB ++
      List.replicate (K - ((encCheck r dsA).length + vB.length + (encCheck r dsB).length)) false) := by
    simp [w, usefulW]
  obtain ⟨b1, b2, _⟩ := chk_encode (encCheck r dsA ++ vB) (List.replicate
    (K - ((encCheck r dsA).length + vB.length + (encCheck r dsB).length)) false) r dsB
  rw [← hw'] at b1 b2
  have hs : startB M N w = (encCheck r dsA ++ vB).length := by
    unfold startB; rw [a3']; simp [hvB]
  exact ⟨a1, a2, by rw [hs]; exact b1, by rw [hs]; exact b2⟩

/-- The useful branch's cost: `c_0N + a_M + 2b_M(t_M+1)` with `c_0 = 607` (proof of `cor:framed-refuter`). -/
def costA (M : OrdinaryWeakMachine) : ℕ :=
  1400 + 30 * ((VerifierEncoding.code M.verifier).length + 2) * (machineIndex M + 2) +
    5000 * ((VerifierEncoding.code M.verifier).length + 1) ^ 2

theorem usefulW_cost (M : OrdinaryWeakMachine) (N t : ℕ) (dsA dsB : List (Fin M.verifier.tapeCount → Bool))
    (vB : List Bool) (K : ℕ) (hvB : vB.length = N / 16) (hA : dsA.length ≤ t) (hB : dsB.length ≤ t) :
    bodyCost M N (usefulW M.verifier.tapeCount (t + 2) dsA dsB vB K) ≤
      607 * N + costA M + 2 * checkerCost M.verifier 3 1 * (t + 1) := by
  obtain ⟨p1, p2, p3, p4⟩ := usefulW_parse M N (t + 2) dsA dsB vB K hvB
  unfold bodyCost costA
  rw [p1, p2, p3, p4]
  have c1 := checkerCost_mono M.verifier (le_refl (t + 2)) hA
  have c2 := checkerCost_mono M.verifier (le_refl (t + 2)) hB
  have c3 := checkerCost_lin M.verifier t
  have hN : N / 16 * 16 ≤ N := Nat.div_mul_le_self N 16
  rw [show 2 * checkerCost M.verifier 3 1 * (t + 1) = 2 * (checkerCost M.verifier 3 1 * (t + 1)) by ring]
  generalize checkerCost M.verifier (t + 2) dsA.length = X1 at c1 ⊢
  generalize checkerCost M.verifier (t + 2) dsB.length = X2 at c2 ⊢
  generalize checkerCost M.verifier (t + 2) t = X3 at c1 c2 c3 ⊢
  generalize checkerCost M.verifier 3 1 * (t + 1) = X4 at c3 ⊢
  generalize 30 * ((VerifierEncoding.code M.verifier).length + 2) * (machineIndex M + 2) = Y1
  generalize 5000 * ((VerifierEncoding.code M.verifier).length + 1) ^ 2 = Y2
  omega

theorem encCheck_le (t : ℕ) (r : ℕ) (ds : List (Fin t → Bool)) (n : ℕ) (h : ds.length ≤ n) :
    (encCheck r ds).length ≤ r + 2 + n * (1 + t) := by
  rw [encCheck_length]; have := Nat.mul_le_mul_right (1 + t) h; omega

/-- **Completeness at one record** (proof of `lem:multitape-refuter`; proof of `cor:framed-refuter`): the useful guess exists, has the prescribed
length, and costs `≤ c_0N + a_M + 2b_M(t_M+1)`. -/
theorem useful_exists (T : ℕ → ℕ) (M : OrdinaryWeakMachine) (N i : ℕ) (hrt : M.runtime N ≤ T N)
    (hhit : hitData M T N i = false) (hmem : i + 1 < 2 ^ (N / 16) → memberData M N (i + 1) = true) (K : ℕ)
    (hK : 2 * (M.runtime N + 4 + M.runtime N * (1 + M.verifier.tapeCount)) + N / 16 ≤ K) :
    ∃ w : List Bool, w.length = K ∧ BodyCond M N i w ∧
      bodyCost M N w ≤ 607 * N + costA M + 2 * checkerCost M.verifier 3 1 * (M.runtime N + 1) := by
  set t := M.runtime N with ht
  set v := M.verifier with hvv
  -- the first simulation
  obtain ⟨trA, hlenA, hchkA, haccA⟩ := weak_trace_useful M N (record M N 0) (unrank (N / 16) i)
  have haccA' : v.accepting (controlAfter v.machine.start trA) = false := by
    cases h : v.accepting (controlAfter v.machine.start trA)
    · rfl
    · exfalso
      have := acceptsAt_mono v hrt _ _ (haccA.mp h)
      unfold hitData at hhit
      simp only [decide_eq_false_iff_not] at hhit
      exact hhit this
  have htrA : traceOfD v.machine v.machine.start (trA.map (·.scanned)) = trA :=
    traceOfD_of_legal v.machine v.machine.start trA hchkA.1
  -- the second simulation
  have hB : ∃ (vB : List Bool) (dsB : List (Fin v.tapeCount → Bool)), vB.length = N / 16 ∧ dsB.length ≤ t ∧
      (i + 1 < 2 ^ (N / 16) → TraceChecks v.machine (t + 2) (v.inputTapes (List.ofFn (record M N (i + 1))) vB)
        (traceOfD v.machine v.machine.start dsB) ∧
        v.accepting (controlAfter v.machine.start (traceOfD v.machine v.machine.start dsB)) = true) := by
    by_cases hlt : i + 1 < 2 ^ (N / 16)
    · have hm := hmem hlt
      unfold memberData machineValue at hm
      simp only [decide_eq_true_eq] at hm
      obtain ⟨vv, hvv'⟩ := (accepts_iff_bounded M N _).mp hm
      obtain ⟨trB, hlenB, hchkB, haccB⟩ := weak_trace_useful M N (record M N (i + 1)) vv
      refine ⟨List.ofFn vv, trB.map (·.scanned), by simp, by simpa using hlenB, fun _ => ?_⟩
      rw [traceOfD_of_legal v.machine v.machine.start trB hchkB.1]
      exact ⟨hchkB, haccB.mpr hvv'⟩
    · exact ⟨List.replicate (N / 16) false, [], by simp, by simp, fun h => absurd h hlt⟩
  obtain ⟨vB, dsB, hvB, hdsB, hBc⟩ := hB
  refine ⟨usefulW v.tapeCount (t + 2) (trA.map (·.scanned)) dsB vB K, ?_, ?_, ?_⟩
  · apply usefulW_length
    have e1 := encCheck_le v.tapeCount (t + 2) (trA.map (·.scanned)) t (by simpa using hlenA)
    have e2 := encCheck_le v.tapeCount (t + 2) dsB t hdsB
    rw [hvB]
    generalize t * (1 + v.tapeCount) = Z at e1 e2 hK
    omega
  · apply usefulW_cond M N i (t + 2) _ _ vB K hvB _ hBc
    rw [htrA]; exact ⟨hchkA, haccA'⟩
  · exact usefulW_cost M N t _ dsB vB K hvB (by simpa using hlenA) hdsB

/-! ## The recurrence -/

set_option maxHeartbeats 400000 in
/-- **`HierarchyRecurrence` for the hierarchy verifier `𝒟`** (proof of `cor:framed-refuter` at every clock with `N ≤ T(N)`, the
cap `1024(T(N)+1)` being `(c_0+2)(T(N)+1)` with `c_0 = 1022`). -/
theorem hierarchyRecurrence (hcr : CappedMachineRun) (T : ℕ → ℕ) (hT : ∀ n, n ≤ T n) (C : ℕ)
    (wf : RepairOrdinary.WordFunction ℕ (fun n => List.replicate n true) (fun n => (T n).bits) (fun n => C * (T n + 1))) :
    HierarchyRecurrence T (hierarchyOf hcr T hT C wf) := by
  intro M hM
  obtain ⟨o1, h1⟩ := useful_branch_fits_cap T hT 1022 M hM (costA M) (checkerCost M.verifier 3 1)
  obtain ⟨o2, h2⟩ := hM (2 * (2 + M.verifier.tapeCount)) (by omega)
  obtain ⟨o3, h3⟩ := hM 1 (by omega)
  refine ⟨max o1 (max o2 (max o3 (2 * (machineIndex M + 2) + 16))), fun N hN i hi => ?_⟩
  have hN1 : o1 ≤ N := le_of_max_le_left hN
  have hN2 : o2 ≤ N := le_of_max_le_left (le_of_max_le_right hN)
  have hN3 : o3 ≤ N := le_of_max_le_left (le_of_max_le_right (le_of_max_le_right hN))
  have hN4 : 2 * (machineIndex M + 2) + 16 ≤ N := le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hN))
  have hv : machineIndex M + 2 + N / 16 ≤ N := by omega
  have hg1 : 1 ≤ N / 16 := by omega
  have hrt : M.runtime N ≤ T N := by simpa using h3 N hN3
  unfold diagData
  apply Bool.eq_iff_iff.mpr
  rw [hierarchy_lang]
  constructor
  · rintro ⟨w, hw⟩
    exact bodyCond_rhs T M N i _ (bodyAcc_sound M N i _ _ hv hg1 hi hw)
  · intro hrhs
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hrhs
    obtain ⟨hhit, hrest⟩ := hrhs
    have hmem : i + 1 < 2 ^ (N / 16) → memberData M N (i + 1) = true := by
      intro hlt; rw [if_pos hlt] at hrest; exact hrest
    have hK : 2 * (M.runtime N + 4 + M.runtime N * (1 + M.verifier.tapeCount)) + N / 16 ≤ hcoef C * (T N + 1) := by
      have a1 := h2 N hN2
      have a2 := hT N
      have a3 : 2002000 * (T N + 1) ≤ hcoef C * (T N + 1) := Nat.mul_le_mul_right _ (by unfold hcoef; omega)
      have e1 : 2 * (2 + M.verifier.tapeCount) * M.runtime N = 4 * M.runtime N + 2 * (M.runtime N * M.verifier.tapeCount) := by
        ring
      have e2 : M.runtime N * (1 + M.verifier.tapeCount) = M.runtime N + M.runtime N * M.verifier.tapeCount := by ring
      rw [e1] at a1; rw [e2]
      generalize M.runtime N * M.verifier.tapeCount = P at a1 ⊢
      generalize hcoef C * (T N + 1) = Q at a3 ⊢
      omega
    obtain ⟨wl, hlen, hcond, hcost⟩ := useful_exists T M N i hrt hhit hmem _ hK
    refine ⟨fun j => wl[j.val]'(by rw [hlen]; exact j.isLt), ?_⟩
    have hof : List.ofFn (fun j : Fin (hcoef C * (T N + 1)) => wl[j.val]'(by rw [hlen]; exact j.isLt)) = wl :=
      List.ext_getElem (by simp [hlen]) (fun j _ _ => by simp)
    rw [hof]
    apply bodyAcc_complete M N i wl _ hv hg1 hi hcond
    have := h1 N hN1
    unfold clockLen
    generalize 2 * checkerCost M.verifier 3 1 * (M.runtime N + 1) = B at this hcost
    omega

/-- **The join `HierarchyRecurrence`, at every admissible clock** (consumer: `clw20_theorem1_13_of_parts`), docked on
the join `CappedMachineRun` (`Joins/CappedRun.lean`). -/
theorem hierarchyRecurrence_of_capped (hcr : CappedMachineRun) :
    ∀ T : ℕ → ℕ, TimeConstructible T → InClockRange T → ∃ H : OrdinaryHierarchy T, HierarchyRecurrence T H := by
  rintro T ⟨C, _, ⟨wf⟩⟩ ⟨hT, _⟩
  exact ⟨hierarchyOf hcr T hT C wf, hierarchyRecurrence hcr T hT C wf⟩

end NearCubicGates.Adapters.Refuter.Clock
