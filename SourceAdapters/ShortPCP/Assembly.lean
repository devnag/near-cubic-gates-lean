import SourceAdapters.ShortPCP.Field6
import SourceAdapters.ShortPCP.AssemblyRun
import SourceAdapters.ShortPCP.Branch
import SourceAdapters.Code.Composition
import SourceAdapters.Code.PolynomialCosts
import SourceAdapters.Proximity.LengthPrefix

/-!
# The top-level ordinary machine of the short PCP

The constructor of `thm:short-pcp-ours`, Step 4, is implemented on the binary-clock
input of `app:short-pcp-proof`, "The exact Lean interface". Its input is
`fr(x) fr(bits t)` with `n ≤ t`.

The machine first tests cell 1 (`n ≥ 1`) and then cell 5 (`n ≥ 2`) using
`Branch.branch`. For `n ≤ 1`, `Branch.constWriter` writes the zero-input,
one-node constant-false circuit. For `n ≥ 2`, paid `Code.composeFramed` calls run
the instance generator, `Proximity.LengthPrefix`, the middle program `Assembly.mid`
with its mask-machine call, and the computation-to-circuit compiler. The middle
program writes the exact request `(data, ℓ, fuel)` specified by `Pipeline.compRequest`.

On promised requests, every allocation and callee budget is bounded polynomially
by the compilation-request measure, itself at most `KB·(n + natBitLength t + 1)^eB`
under the `AssemblyMachine` contract. One program handles every input length.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.ShortPCP.OracleCircuitPCP

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.Bindings.MW20
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters.Joins.SingleRun NearCubicGates.Adapters.Compile
open NearCubicGates.Close.Cells NearCubicGates.Adapters.ShortPCP.Assembly
open NearCubicGates.Adapters.Code.PolynomialCosts
open NearCubicGates.Adapters.ACSP.Affine

/-! ## The code word and the run data -/

/-- The part of the code word after `natWord f`. -/
def codeRest (c : Instance) : List Bool :=
  natWord c.irr ++ listWord natWord c.hBasis ++ natWord c.hOffset ++
    listWord Instance.pairWord c.nbr ++ listWord gateWord c.cons ++
    listWord natWord c.iBasis ++ natWord c.iOffset

theorem code_word (c : Instance) : c.word = natWord c.f ++ codeRest c := by
  simp [Instance.word, codeRest, List.append_assoc]

/-- With the modulus bit `irr_f = 1`, `f` is below the length of the code word. -/
theorem f_lt_word (c : Instance) (h : c.irr.testBit c.f = true) : c.f < c.word.length := by
  have h1 : 2 ^ c.f ≤ c.irr := Nat.ge_two_pow_of_testBit h
  have h2 : c.f + 1 ≤ natBitLength c.irr := by
    unfold natBitLength
    have := Nat.le_log_of_pow_le (by norm_num) h1
    omega
  have h3 : (natWord c.irr).length ≤ c.word.length := by
    rw [code_word]; simp [codeRest]; omega
  rw [NearCubicGates.Close.Cells.natWord_length] at h3; omega

/-- The data of the middle program for the request `r`. -/
def runOf (P : Pipeline) (r : ClockRequest) : Run where
  xb := P.xbar r
  cw := (P.inst r).word
  rest := codeRest (P.inst r)
  f := (P.inst r).f
  n := r.1.1
  S := masksOf (r0f (P.inst r).f) (P.inst r).f r.1.1 P.K1 P.b1
  c0 := natBitLength P.KL
  bL := P.bL
  KT := P.KT
  eT := P.eT

theorem runOf_ell (P : Pipeline) (r : ClockRequest) : (runOf P r).ell = P.ell r := rfl

section Promise

variable (P : Pipeline) (r : ClockRequest) (hr0 : r0 (P.inst r) = r0f (P.inst r).f)
  (hdB : dH (P.inst r) = 2 ^ ((P.inst r).f - 2))
include hr0 hdB

theorem runOf_data : (runOf P r).data = (P.request r).data := by
  simp only [Run.data, Run.sWord, runOf, Pipeline.request, SingleRun.request, Request.data, hdB, masks_eq_masksOf, hr0]
  rfl

theorem runOf_fuel : (runOf P r).fuel = (P.compRequest r).fuel := by
  simp only [Run.fuel, runOf_data P r hr0 hdB]; rfl

theorem runOf_out : (runOf P r).out = frame (P.compRequest r).word := by
  simp only [Run.out, runOf_data P r hr0 hdB, runOf_fuel P r hr0 hdB, runOf_ell, OracleCompilationRequest.word]
  rfl

end Promise

/-! ## The callee, the sizes, the context -/

/-- P05's mask machine as the callee of the middle program. -/
def maskCallee (P : Pipeline) (KM eM : ℕ)
    (gM : OrdinaryWordFunction (ℕ × ℕ) maskWord (fun q => listWord frame (masksOf (r0f q.1) q.1 q.2 P.K1 P.b1))
      (fun q => KM * (q.1 + q.2 + 1) ^ eM)) : Callee :=
  ⟨ℕ × ℕ, maskWord, fun q => listWord frame (masksOf (r0f q.1) q.1 q.2 P.K1 P.b1),
    fun q => KM * (q.1 + q.2 + 1) ^ eM, gM⟩

/-- The cell sizes: width `a1·X`, call input `8·X`, call budget `KM·2^{eM}·X^{eM}` for `X = 2^{leading ones}`. -/
def sizes (a1 KM eM : ℕ) : Sz := ⟨a1, 1, 8, 1, KM * 2 ^ eM, eM⟩

/-- The middle program's input: the length header and `w = frame x̄ ++ code`. -/
def midIn (P : Pipeline) (r : ClockRequest) : List Bool := natWord (runOf P r).w.length ++ (runOf P r).w

theorem leadOnes_rep' (k : ℕ) (l : List Bool) : leadOnes (List.replicate k true ++ false :: l) = k := by
  induction k with
  | zero => simp [leadOnes]
  | succ k ih => simp [List.replicate_succ, leadOnes, ih]

theorem leadOnes_natWord (v : ℕ) (rest : List Bool) : leadOnes (natWord v ++ rest) = natBitLength v := by
  rw [NearCubicGates.Close.Cells.natWord_eq, List.append_assoc, List.cons_append]
  exact leadOnes_rep' _ _

/-- `X = 2^{natBitLength |w|}`. -/
def bigX (P : Pipeline) (r : ClockRequest) : ℕ := 2 ^ natBitLength (runOf P r).w.length

theorem lead_midIn (P : Pipeline) (r : ClockRequest) : leadOnes (midIn P r) = natBitLength (runOf P r).w.length :=
  leadOnes_natWord _ _

theorem w_lt_X (P : Pipeline) (r : ClockRequest) : (runOf P r).w.length < bigX P r :=
  NearCubicGates.Close.Cells.lt_natBitLength _

theorem one_le_X (P : Pipeline) (r : ClockRequest) : 1 ≤ bigX P r := Nat.one_le_two_pow

theorem X_le_w (P : Pipeline) (r : ClockRequest) : bigX P r ≤ 2 * (runOf P r).w.length + 2 := by
  unfold bigX natBitLength
  have := Nat.pow_log_le_self 2 (show (runOf P r).w.length + 1 ≠ 0 by omega)
  rcases Nat.eq_zero_or_pos (runOf P r).w.length with h | h
  · rw [h]; simp
  · have h2 := Nat.pow_log_le_self 2 (show (runOf P r).w.length ≠ 0 by omega)
    rw [pow_succ]; omega

/-! ## The promise and the sizes on promised requests -/

/-- The promise on a request (the hypothesis of `AssemblyMachine`, with `2 ≤ n ≤ t`). -/
def Prom (P : Pipeline) (KB eB : ℕ) (r : ClockRequest) : Prop :=
  2 ≤ r.1.1 ∧ r.1.1 ≤ r.2 ∧ (∃ j, P.xbar r = List.ofFn r.1.2 ++ true :: List.replicate j false) ∧
    r0 (P.inst r) = r0f (P.inst r).f ∧ dH (P.inst r) = 2 ^ ((P.inst r).f - 2) ∧
    (P.compRequest r).measure ≤ KB * (r.1.1 + natBitLength r.2 + 1) ^ eB ∧
    2 ≤ (P.inst r).f ∧ (P.inst r).irr.testBit (P.inst r).f = true

theorem prom_wl (P : Pipeline) (r : ClockRequest) :
    (runOf P r).w.length = (RepairOrdinary.frame (P.xbar r)).length + (P.inst r).word.length := by
  simp [Run.w, runOf]

section Sizes

variable {P : Pipeline} {KB eB : ℕ} {r : ClockRequest} (h : Prom P KB eB r)
include h

theorem prom_n : lastTrue (P.xbar r) 0 0 = r.1.1 := by
  obtain ⟨j, hj⟩ := h.2.2.1
  rw [hj, lastTrue_padded, List.length_ofFn]

theorem prom_n_lt : r.1.1 < (P.xbar r).length := by
  obtain ⟨j, hj⟩ := h.2.2.1
  rw [hj]; simp

theorem prom_f_lt : (P.inst r).f < (runOf P r).w.length := by
  have := f_lt_word (P.inst r) h.2.2.2.2.2.2.2
  rw [prom_wl]; omega

theorem prom_n_lt_w : r.1.1 < (runOf P r).w.length := by
  have := prom_n_lt h; have := frame_length' (P.xbar r)
  rw [prom_wl]; omega

end Sizes

/-- The step bound `U` of the middle program on the request `r` (cell sizes from `L = natBitLength |w|`). -/
def bigU (P : Pipeline) (KM eM : ℕ) (r : ClockRequest) : ℕ :=
  (runOf P r).bound + 50 * (2 ^ (1 * natBitLength (runOf P r).w.length) * 8 +
    2 ^ (eM * natBitLength (runOf P r).w.length) * (KM * 2 ^ eM))

theorem two_pow_L (P : Pipeline) (r : ClockRequest) : 2 ^ (1 * natBitLength (runOf P r).w.length) = bigX P r := by
  rw [one_mul]; rfl

theorem two_pow_eL (P : Pipeline) (eM : ℕ) (r : ClockRequest) :
    2 ^ (eM * natBitLength (runOf P r).w.length) = bigX P r ^ eM := by
  rw [Nat.mul_comm, pow_mul]; rfl

theorem sWord_le (P : Pipeline) (KM eM : ℕ)
    (gM : OrdinaryWordFunction (ℕ × ℕ) maskWord (fun q => listWord frame (masksOf (r0f q.1) q.1 q.2 P.K1 P.b1))
      (fun q => KM * (q.1 + q.2 + 1) ^ eM)) (r : ClockRequest) :
    (runOf P r).sWord.length ≤ KM * ((P.inst r).f + r.1.1 + 1) ^ eM + 1 :=
  wf_out_len gM ((P.inst r).f, r.1.1)

/-- **The inner size bound**: `U ≤ K (X + 1)^e` on promised requests, for constants depending only on the pipeline
and the machines' constants. -/
theorem bigU_bound (P : Pipeline) (KB eB KM eM : ℕ)
    (gM : OrdinaryWordFunction (ℕ × ℕ) maskWord (fun q => listWord frame (masksOf (r0f q.1) q.1 q.2 P.K1 P.b1))
      (fun q => KM * (q.1 + q.2 + 1) ^ eM)) {R : Type} (g : R → ClockRequest) (hg : ∀ x, Prom P KB eB (g x)) :
    Bound (fun x => bigX P (g x)) (fun x => bigU P KM eM (g x)) := by
  set X := fun x => bigX P (g x) with hXdef
  have hX : Bound X X := self
  have hw : ∀ x, (runOf P (g x)).w.length ≤ X x := fun x => (w_lt_X P (g x)).le
  have hf : Bound X (fun x => (P.inst (g x)).f) := mono hX (fun x => ((prom_f_lt (hg x)).trans (w_lt_X P (g x))).le)
  have hn : Bound X (fun x => (g x).1.1) := mono hX (fun x => ((prom_n_lt_w (hg x)).trans (w_lt_X P (g x))).le)
  have hinp : Bound X (fun x => (natWord (runOf P (g x)).w.length ++ (runOf P (g x)).w).length) := by
    refine mono (add (mul (constant 3) hX) (constant 3)) (fun x => ?_)
    have h1 := hw x
    have h2 := nbl_le' (runOf P (g x)).w.length
    simp only [List.length_append, NearCubicGates.Close.Cells.natWord_length]; omega
  have hS : Bound X (fun x => (runOf P (g x)).sWord.length) := by
    refine mono (add (mul (constant KM) (pow (add (add hf hn) (constant 1)) eM)) (constant 1)) (fun x => ?_)
    exact sWord_le P KM eM gM (g x)
  have hdata : Bound X (fun x => (runOf P (g x)).data.length) := by
    refine mono (add (add hX (mul (constant 2) hf)) hS) (fun x => ?_)
    have e1 := data_length (runOf P (g x)) (hg x).2.2.2.2.2.2.1
    have e2 : (runOf P (g x)).sWord.length =
        (natWord (runOf P (g x)).S.length).length + (framesWord (runOf P (g x)).S).length := by simp [Run.sWord]
    have e3 : (runOf P (g x)).w.length =
        (runOf P (g x)).cw.length + (RepairOrdinary.frame (runOf P (g x)).xb).length := by
      simp [Run.w]; omega
    have e4 : (runOf P (g x)).f = (P.inst (g x)).f := rfl
    have := hw x
    omega
  have hk : Bound X (fun x => natBitLength (P.inst (g x)).f) := mono (add hf (constant 1)) (fun x => nbl_le' _)
  have hell : Bound X (fun x => (runOf P (g x)).ell) := by
    refine mono (add (add (constant (natBitLength P.KL)) hf) (mul (constant P.bL) hk)) (fun x => ?_)
    simp [Run.ell, runOf]
  have hfuel : Bound X (fun x => (runOf P (g x)).fuel) := by
    refine mono (mul (constant P.KT) (pow (add (add hdata hell) (constant 1)) P.eT)) (fun x => ?_)
    simp [Run.fuel, runOf]
  have hbound : Bound X (fun x => (runOf P (g x)).bound) := by
    unfold Run.bound
    exact mul (constant 50) (add (add (add (add (add (add (add (add hinp hdata) hell) hfuel) (constant _))
      (constant _)) (constant _)) (constant _)) (constant 10))
  refine mono (add hbound (mul (constant 50) (add (mul hX (constant 8)) (mul (pow hX eM) (constant (KM * 2 ^ eM))))))
    (fun x => ?_)
  unfold bigU
  rw [two_pow_L, two_pow_eL]

/-! ## The middle program as an ordinary word function -/

section Cells

variable (P : Pipeline) (KB eB KM eM : ℕ)
  (gM : OrdinaryWordFunction (ℕ × ℕ) maskWord (fun q => listWord frame (masksOf (r0f q.1) q.1 q.2 P.K1 P.b1))
    (fun q => KM * (q.1 + q.2 + 1) ^ eM))

theorem ctx_W (a1 : ℕ) (r : ClockRequest) :
    (ctxOf (maskCallee P KM eM gM) (sizes a1 KM eM) (midIn P r)).Wd = bigX P r * a1 := by
  show 2 ^ (1 * leadOnes (midIn P r)) * a1 = _; rw [lead_midIn, two_pow_L]

theorem ctx_Lk (a1 : ℕ) (r : ClockRequest) :
    (ctxOf (maskCallee P KM eM gM) (sizes a1 KM eM) (midIn P r)).Lk = bigX P r * 8 := by
  show 2 ^ (1 * leadOnes (midIn P r)) * 8 = _; rw [lead_midIn, two_pow_L]

theorem ctx_Bk (a1 : ℕ) (r : ClockRequest) :
    (ctxOf (maskCallee P KM eM gM) (sizes a1 KM eM) (midIn P r)).Bk = bigX P r ^ eM * (KM * 2 ^ eM) := by
  show 2 ^ (eM * leadOnes (midIn P r)) * (KM * 2 ^ eM) = _; rw [lead_midIn, two_pow_eL]

theorem midIn_length (r : ClockRequest) : (midIn P r).length ≤ 3 * bigX P r + 3 := by
  have h1 := w_lt_X P r
  have h2 := nbl_le' (runOf P r).w.length
  simp only [midIn, List.length_append, NearCubicGates.Close.Cells.natWord_length]; omega

/-- **The certificate of one run.** -/
theorem runGood (r : ClockRequest) (h : Prom P KB eB r) (a1 : ℕ) (ha1 : 4 * bigU P KM eM r < 2 ^ (bigX P r * a1))
    (ha8 : 8 ≤ a1) :
    (runOf P r).Good (ctxOf (maskCallee P KM eM gM) (sizes a1 KM eM) (midIn P r)) (bigU P KM eM r) := by
  have hX1 := one_le_X P r
  have hwX := w_lt_X P r
  have hfX := (prom_f_lt h).trans hwX
  have hnX := (prom_n_lt_w h).trans hwX
  refine ⟨rfl, code_word _, prom_n h, h.2.2.2.2.2.2.1, ⟨((P.inst r).f, r.1.1), rfl, rfl, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- the callee's budget
    show KM * ((P.inst r).f + r.1.1 + 1) ^ eM ≤ _
    rw [ctx_Bk]
    have : ((P.inst r).f + r.1.1 + 1) ^ eM ≤ (2 * bigX P r) ^ eM := Nat.pow_le_pow_left (by omega) eM
    rw [mul_pow] at this
    calc KM * ((P.inst r).f + r.1.1 + 1) ^ eM ≤ KM * (2 ^ eM * bigX P r ^ eM) := Nat.mul_le_mul_left KM this
      _ = _ := by ring
  · -- the call input
    rw [ctx_Lk]
    have h1 := nbl_le' (P.inst r).f
    have h2 := nbl_le' r.1.1
    simp only [runOf, NearCubicGates.Close.Cells.natWord_length]; omega
  · -- the step bound
    show _ ≤ bigU P KM eM r
    rw [ctx_Lk, ctx_Bk]; unfold bigU; rw [two_pow_L, two_pow_eL]
  · rw [ctx_W]; exact ha1
  · show (midIn P r).length + 2 ≤ _
    rw [ctx_W]
    have := midIn_length P r
    nlinarith

/-- The width that makes every run fit: from the inner bound `U ≤ K (X + 1)^e`, `4 U < 2^{X (4K + e + 8)}`. -/
theorem width_ok (K e U X : ℕ) (hX : 1 ≤ X) (hU : U ≤ K * (X + 1) ^ e) : 4 * U < 2 ^ (X * (4 * K + e + 8)) := by
  have h1 : X + 1 ≤ 2 ^ X := Nat.lt_two_pow_self
  have h2 : (X + 1) ^ e ≤ 2 ^ (X * e) := by rw [pow_mul]; exact Nat.pow_le_pow_left h1 e
  have h3 : 4 * K < 2 ^ (4 * K) := Nat.lt_two_pow_self
  have h4 : 1 ≤ (X + 1) ^ e := Nat.one_le_pow _ _ (by omega)
  have h5 : 4 * K * (X + 1) ^ e < 2 ^ (4 * K) * 2 ^ (X * e) :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h3 h4) (Nat.mul_le_mul_left _ h2)
  have h6 : 2 ^ (4 * K) * 2 ^ (X * e) ≤ 2 ^ (X * (4 * K + e + 8)) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  calc 4 * U ≤ 4 * K * (X + 1) ^ e := by rw [mul_assoc]; exact Nat.mul_le_mul_left 4 hU
    _ < _ := lt_of_lt_of_le h5 h6

/-- **The middle program as an ordinary word function** on promised requests. -/
theorem cells_wf {R : Type} (g : R → ClockRequest) (hg : ∀ x, Prom P KB eB (g x)) :
    ∃ a1 K e : ℕ, 8 ≤ a1 ∧ (∀ x, bigU P KM eM (g x) ≤ K * (bigX P (g x) + 1) ^ e) ∧
      Nonempty (OrdinaryWordFunction R (fun x => midIn P (g x)) (fun x => frame (P.compRequest (g x)).word)
        (fun x => langBudget (maskCallee P KM eM gM) (sizes a1 KM eM) VV MM (midIn P (g x))
          (57 * (bigU P KM eM (g x) + 1)))) := by
  obtain ⟨K, e, hKe⟩ := bigU_bound P KB eB KM eM gM g hg
  refine ⟨4 * K + e + 8, K, e, by omega, hKe, ⟨?_⟩⟩
  refine wordFunction_of_lang (fun x => midIn P (g x)) (fun x => frame (P.compRequest (g x)).word)
    (maskCallee P KM eM gM) (sizes (4 * K + e + 8) KM eM) (mid (natBitLength P.KL) P.bL P.KT P.eT)
    (fun x => 57 * (bigU P KM eM (g x) + 1)) (fun x => ?_) (fun x => ?_)
  · have hgood := runGood P KB eB KM eM gM (g x) (hg x) (4 * K + e + 8)
      (width_ok K e _ _ (one_le_X P (g x)) (hKe x)) (by omega)
    obtain ⟨b, n, hex, hn, hb⟩ := mid_spec (runOf P (g x)) (bigU P KM eM (g x)) hgood
    refine ⟨b, n, hex, ?_, hn⟩
    rw [hb, runOf_out P (g x) (hg x).2.2.2.1 (hg x).2.2.2.2.1]
  · show 1 ≤ 2 ^ (1 * leadOnes (midIn P (g x))) * (4 * K + e + 8)
    have := Nat.one_le_two_pow (n := 1 * leadOnes (midIn P (g x)))
    nlinarith

end Cells

/-! ## The composed machine on promised requests -/

theorem nbl_le_bits (t : ℕ) : natBitLength t ≤ t.bits.length + 1 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [natBitLength]
  · have h1 : t < 2 ^ t.bits.length := by
      have := Nat.lt_size_self t; rwa [← Nat.size_eq_bits_len] at this
    have := Nat.log_lt_of_lt_pow (by omega) h1
    unfold natBitLength; omega

theorem word_size (r : ClockRequest) : r.1.1 + natBitLength r.2 ≤ r.word.length := by
  have h1 := nbl_le_bits r.2
  simp only [ClockRequest.word, List.length_append, frame_length, List.length_ofFn]; omega

theorem w_le_measure (P : Pipeline) (KB eB : ℕ) (r : ClockRequest) (h : Prom P KB eB r) :
    (runOf P r).w.length ≤ (P.compRequest r).measure := by
  have h1 : (runOf P r).w.length ≤ (runOf P r).data.length := by
    simp only [Run.w, Run.data, List.length_append]; omega
  rw [runOf_data P r h.2.2.2.1 h.2.2.2.2.1] at h1
  unfold OracleCompilationRequest.measure
  have e : (P.compRequest r).data = (P.request r).data := rfl
  rw [e]; omega

section Main

variable (P : Pipeline) (KS eS KM eM KX dX KB eB : ℕ)
  (gS : OrdinaryWordFunction ClockRequest ClockRequest.word
    (fun r => frame (frame (P.xbar r) ++ (P.inst r).word)) (fun r => KS * (r.1.1 + natBitLength r.2 + 1) ^ eS))
  (gM : OrdinaryWordFunction (ℕ × ℕ) maskWord (fun q => listWord frame (masksOf (r0f q.1) q.1 q.2 P.K1 P.b1))
    (fun q => KM * (q.1 + q.2 + 1) ^ eM))
  (gX : OrdinaryWordFunction OracleCompilationRequest OracleCompilationRequest.word
    (fun q => OracleOutput.word ⟨q.ell, P.circuit q⟩) (fun q => KX * q.measure ^ dX))
include gS gM gX

/-- **The machine for `n ≥ 2`**: P03's generator, the length header, the middle program (with P05's mask machine)
and X5(a)'s generator, composed; its budget is polynomial in the input length. -/
theorem main_wf {R : Type} (g : R → ClockRequest) (hg : ∀ x, Prom P KB eB (g x)) :
    ∃ K e : ℕ, Nonempty (OrdinaryWordFunction R (fun x => (g x).word) (fun x => (P.pcpOutput (g x)).word)
      (fun x => K * ((g x).word.length + 1) ^ e)) := by
  let m : R → ℕ := fun x => (g x).word.length
  have hm : ∀ x, (g x).1.1 + natBitLength (g x).2 + 1 ≤ m x + 1 := fun x => by
    have := word_size (g x); show _ ≤ (g x).word.length + 1; omega
  have hmeas : Bound m (fun x => (P.compRequest (g x)).measure) :=
    mono (mul (constant KB) (pow (add self (constant 1)) eB)) (fun x =>
      (hg x).2.2.2.2.2.1.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hm x) _)))
  have hw : Bound m (fun x => (runOf P (g x)).w.length) := mono hmeas (fun x => w_le_measure P KB eB (g x) (hg x))
  have hX : Bound m (fun x => bigX P (g x)) :=
    mono (add (mul (constant 2) hw) (constant 2)) (fun x => X_le_w P (g x))
  obtain ⟨a1, K, e, -, hKe, ⟨WC⟩⟩ := cells_wf P KB eB KM eM gM g hg
  have bS : Bound m (fun x => KS * ((g x).1.1 + natBitLength (g x).2 + 1) ^ eS) :=
    mono (mul (constant KS) (pow (add self (constant 1)) eS)) (fun x =>
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hm x) _))
  have bP : Bound m (fun x => 10000 * ((runOf P (g x)).w.length + 1) ^ 2) :=
    mono (mul (constant 10000) (pow (add hw (constant 1)) 2)) (fun x => le_rfl)
  have bX : Bound m (fun x => KX * (P.compRequest (g x)).measure ^ dX) :=
    mono (mul (constant KX) (pow hmeas dX)) (fun x => le_rfl)
  have bC : Bound m (fun x => langBudget (maskCallee P KM eM gM) (sizes a1 KM eM) VV MM (midIn P (g x))
      (57 * (bigU P KM eM (g x) + 1))) := by
    refine language (maskCallee P KM eM gM) (sizes a1 KM eM) VV MM (fun x => midIn P (g x))
      (fun x => 57 * (bigU P KM eM (g x) + 1)) ?_ ?_ ?_ ?_ ?_ ?_
    · refine mono (add hw (constant 1)) (fun x => ?_)
      rw [lead_midIn]; exact nbl_le' _
    · refine mono (mul hX (constant a1)) (fun x => ?_)
      show 2 ^ (1 * leadOnes (midIn P (g x))) * a1 ≤ _
      rw [lead_midIn, two_pow_L]
    · refine mono (mul hX (constant 8)) (fun x => ?_)
      show 2 ^ (1 * leadOnes (midIn P (g x))) * 8 ≤ _
      rw [lead_midIn, two_pow_L]
    · refine mono (mul (pow hX eM) (constant (KM * 2 ^ eM))) (fun x => ?_)
      show 2 ^ (eM * leadOnes (midIn P (g x))) * (KM * 2 ^ eM) ≤ _
      rw [lead_midIn, two_pow_eL]
    · exact mono (add (mul (constant 3) hX) (constant 3)) (fun x => midIn_length P (g x))
    · exact mono (mul (constant 57) (add (mul (constant K) (pow (add hX (constant 1)) e)) (constant 1)))
        (fun x => Nat.mul_le_mul_left 57 (by have := hKe x; omega))
  let WS := Branch.pull g gS
  let WP := Branch.pull (fun x => (runOf P (g x)).w) Proximity.LengthPrefix.polynomialWordFunction
  let WX := Branch.pull (fun x => P.compRequest (g x)) gX
  let c1 := Code.composeFramed (middle := fun x => (runOf P (g x)).w) WS WP
  let c2 := Code.composeFramed (middle := fun x => midIn P (g x)) c1 WC
  let c3 := Code.composeFramed (middle := fun x => (P.compRequest (g x)).word) c2 WX
  obtain ⟨K1, e1, h1⟩ := Code.composeFramed_budget_poly (fun x => (g x).word) _ _ bS bP
  obtain ⟨K2, e2, h2⟩ := Code.composeFramed_budget_poly (fun x => (g x).word) _ _ ⟨K1, e1, h1⟩ bC
  obtain ⟨K3, e3, h3⟩ := Code.composeFramed_budget_poly (fun x => (g x).word) _ _ ⟨K2, e2, h2⟩ bX
  exact ⟨K3, e3, ⟨c3.enlargeBudget h3⟩⟩

end Main

/-! ## Branching on `n` and the field's machine -/

/-- The same program, with an equal output and a larger budget. -/
def recast {R : Type} {input out1 out2 : R → List Bool} {b1 b2 : R → ℕ} (W : OrdinaryWordFunction R input out1 b1)
    (ho : ∀ r, out1 r = out2 r) (hb : ∀ r, b1 r ≤ b2 r) : OrdinaryWordFunction R input out2 b2 :=
  ⟨(W.enlargeBudget hb).program, fun r => by
    obtain ⟨rc, h1, h2⟩ := (W.enlargeBudget hb).realizes r
    exact ⟨rc, h1, h2.trans (ho r)⟩⟩

/-- Cell 1 of the framed input `fr(fr(x) fr(bits t))` is `1` iff `n ≥ 1`. -/
theorem cell1 (r : ClockRequest) : Branch.cellAt 1 r.word = decide (1 ≤ r.1.1) := by
  have hfx := frame_length (List.ofFn r.1.2)
  simp only [List.length_ofFn] at hfx
  unfold Branch.cellAt
  rw [show (1 : ℕ) = 2 * 0 + 1 from rfl, frame_odd _ 0 (by simp [ClockRequest.word]),
    ClockRequest.word, List.getD_append _ _ _ _ (by omega), show (0 : ℕ) = 2 * 0 from rfl,
    frame_even _ 0 (by omega)]
  simp only [List.length_ofFn, decide_eq_decide]; omega

/-- With `n ≥ 1`, cell 5 is `1` iff `n ≥ 2`. -/
theorem cell5 (r : ClockRequest) (h : 1 ≤ r.1.1) : Branch.cellAt 5 r.word = decide (2 ≤ r.1.1) := by
  have hfx := frame_length (List.ofFn r.1.2)
  simp only [List.length_ofFn] at hfx
  have hw : 2 < r.word.length := by simp only [ClockRequest.word, List.length_append]; omega
  unfold Branch.cellAt
  rw [show (5 : ℕ) = 2 * 2 + 1 from rfl, frame_odd _ 2 hw, ClockRequest.word, List.getD_append _ _ _ _ (by omega),
    show (2 : ℕ) = 2 * 1 from rfl, frame_even _ 1 (by simp; omega)]
  simp only [List.length_ofFn, decide_eq_decide]; omega

/-- **P07 (`AssemblyMachine`)**: the top-level ordinary machine of input 6, from P03's generator, P05's mask machine
and X5(a)'s generator (proof of `thm:short-pcp-ours`; `app:short-pcp-proof`, "The exact Lean interface"). -/
theorem assemblyMachine : AssemblyMachine := by
  intro P KS eS KM eM KX dX KB eB ⟨gS⟩ ⟨gM⟩ ⟨gX⟩ hprom
  let R0 := {r : ClockRequest // r.1.1 ≤ r.2}
  let inp : R0 → List Bool := fun r => r.1.word
  let out : R0 → List Bool := fun r => (P.output r.1).word
  let R1 := {r : R0 // Branch.cellAt 1 (inp r) = true}
  let R2 := {r : R1 // Branch.cellAt 5 (inp r.1) = true}
  have h1 : ∀ r : R1, 1 ≤ r.1.1.1.1 := fun r => by
    have := r.2; simp only [inp, cell1] at this; simpa using this
  have hg : ∀ x : R2, Prom P KB eB x.1.1.1 := fun x => by
    have h2 : 2 ≤ x.1.1.1.1.1 := by
      have := x.2; simp only [inp, cell5 _ (h1 x.1)] at this; simpa using this
    exact ⟨h2, x.1.1.2, hprom x.1.1.1 h2 x.1.1.2⟩
  obtain ⟨K, e, ⟨WM⟩⟩ := main_wf P KS eS KM eM KX dX KB eB gS gM gX (fun x : R2 => x.1.1.1) hg
  let cF : ℕ := 8 * falseOutput.word.length + 2
  let bT : R1 → ℕ := fun r => K * ((inp r.1).length + 1) ^ e
  have T2 : OrdinaryWordFunction R2 (fun x => inp x.1.1) (fun x => out x.1.1) (fun x => bT x.1) :=
    recast WM (fun x => by
      show (P.pcpOutput x.1.1.1).word = (P.output x.1.1.1).word
      rw [Pipeline.output, if_pos (hg x).1]) (fun _ => le_rfl)
  have F2 : OrdinaryWordFunction {r : R1 // Branch.cellAt 5 (inp r.1) = false} (fun x => inp x.1.1)
      (fun x => out x.1.1) (fun _ => cF) :=
    recast (Branch.constWriter (fun x : {r : R1 // Branch.cellAt 5 (inp r.1) = false} => inp x.1.1)
      falseOutput.word) (fun x => by
        have h5 := x.2; simp only [inp, cell5 _ (h1 x.1)] at h5
        show falseOutput.word = (P.output x.1.1.1).word
        rw [Pipeline.output, if_neg (by simpa using h5)]) (fun _ => le_rfl)
  let B1 := Branch.branch (R := R1) (input := fun r => inp r.1) (output := fun r => out r.1) bT (fun _ => cF) 5 T2 F2
  have F1 : OrdinaryWordFunction {r : R0 // Branch.cellAt 1 (inp r) = false} (fun x => inp x.1)
      (fun x => out x.1) (fun _ => cF) :=
    recast (Branch.constWriter (fun x : {r : R0 // Branch.cellAt 1 (inp r) = false} => inp x.1) falseOutput.word)
      (fun x => by
        have h1' := x.2; simp only [inp, cell1] at h1'
        show falseOutput.word = (P.output x.1.1).word
        rw [Pipeline.output, if_neg (by simp at h1'; omega)]) (fun _ => le_rfl)
  let B0 := Branch.branch (R := R0) (input := inp) (output := out)
    (fun r => 2 * (4 * 5 + 4 + K * ((inp r).length + 1) ^ e + cF) + 2) (fun _ => cF) 1 B1 F1
  refine ⟨4 * K + 2 * (4 * 1 + 4 + 2 * (4 * 5 + 4 + cF) + 2 + cF) + 2, e, ⟨B0.enlargeBudget (fun r => ?_)⟩⟩
  have hp : 1 ≤ ((inp r).length + 1) ^ e := Nat.one_le_pow _ _ (by omega)
  show 2 * (4 * 1 + 4 + (2 * (4 * 5 + 4 + K * ((inp r).length + 1) ^ e + cF) + 2) + cF) + 2 ≤ _
  nlinarith

/-- Input 6 from the stated short-PCP interfaces and the proved ordinary assembly machine. -/
theorem shortPCP_of_joins' (hS : ∀ V, AffineConstraintReduction V) (hA : AmplifiedVerifier) (hT : SingleRunTime)
    (hX : ComputationToCircuit) (hTM : OrdinaryToTM2PolyTime) (hM : MaskMachine) : MW20_OracleCircuitPCP_TM2 :=
  shortPCP_of_joins hS hA hT hX hTM hM assemblyMachine

/-- **Input 6 from the BCGT13 leaves, with P07 proved.** -/
theorem shortPCP_of_leaves' (h11 : NearCubicGates.Published.BCGT13.BCGT13_Theorem11_1)
    (hS : ∀ V, AffineConstraintReduction V)
    (hT : SingleRunTime) (hX : ComputationToCircuit) (hM : MaskMachine) : MW20_OracleCircuitPCP_TM2 :=
  shortPCP_of_leaves h11 hS hT hX hM assemblyMachine

end NearCubicGates.Adapters.ShortPCP.OracleCircuitPCP
