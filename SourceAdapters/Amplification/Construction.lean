import SourceAdapters.Amplification.DispProgram
import SourceAdapters.Amplification.EncBound
import SourceAdapters.Amplification.Assembly

/-!
# A05: the amplifier's truth table in `2^{O(n)}` time (`app:sources`, "Full-range amplification interface")

: "Initialization, the capped simulation, integer operations, and reading and writing the framed
arities and truth tables all take `2^{O(n)}` time. […] After increasing its exponent and onset, the bound is
`2^{en}` as required by the companion. The machine never tests whether the input function is hard. Its constants
and onsets may depend on `S`."

The machine is `prep1WF` (word program: width prefix `1^(size n)`), then `unaryWF` (cell program: widen to
`1^(n+4)`), then `dispWF S` (the dispatcher cell program `dispP`, compiled with the capped time constructor of X8
as its callee), composed by `Code.composeFramed`. Its width is `2^((c+1)(n+4))·G` (`dispSz`), enough for the cap
`Cs(2^(n+3) + n^c + D1)` (`disp_width`). Every compiled budget is at most `20000·Y³` when every size parameter is
at most `Y` (`langBudget_le_cube`); from the onset `n0` every parameter is at most `H·2^(F(n+4))`
(`dispN_le`), so the whole budget is at most `2^(e·n)`. `constructionObligation : ConstructionObligation`.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Adapters.Amplification.Enc

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.ExecutableInterfaces
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairSource (amplifierInput)
open NearCubicWires.Bindings.CLW20Lemma39 NearCubicGates.Adapters.Joins

/-! ## A generic bound for compiled budgets -/

theorem langBudget_le_cube (K : Callee) (z : Sz) (inp : List Bool) (N Y : ℕ) (hY : 1 ≤ Y)
    (hL : leadOnes inp ≤ Y) (hW : z.W (leadOnes inp) ≤ Y) (hLk : z.Lk (leadOnes inp) ≤ Y)
    (hBk : z.Bk (leadOnes inp) ≤ Y) (ha : z.a1 + z.a2 + z.a3 + z.c1 + z.c2 + z.c3 ≤ Y) (hT : TSK K ≤ Y)
    (hN : N ≤ Y) (hinp : inp.length ≤ Y) :
    langBudget K z NV 0 inp N ≤ 20000 * Y ^ 3 := by
  unfold langBudget costA costB costC
  simp only
  set L := leadOnes inp
  set W := z.W L
  set Lk := z.Lk L
  set Bk := z.Bk L
  have h1 : L * (60 * W + 11 * z.c1 + 8) ≤ Y * (79 * Y + 8) := Nat.mul_le_mul hL (by omega)
  have h2 : L * (60 * Lk + 11 * z.c2 + 8) ≤ Y * (79 * Y + 8) := Nat.mul_le_mul hL (by omega)
  have h3 : L * (60 * Bk + 11 * z.c3 + 8) ≤ Y * (79 * Y + 8) := Nat.mul_le_mul hL (by omega)
  have h4 : N * (500 * (W + 1) ^ 2 + 100 * (TSK K + 3)) ≤ Y * (500 * (Y + 1) ^ 2 + 100 * (Y + 3)) :=
    Nat.mul_le_mul hN (by have := Nat.pow_le_pow_left (show W + 1 ≤ Y + 1 by omega) 2; omega)
  have e1 : Y * (79 * Y + 8) = 79 * Y ^ 2 + 8 * Y := by ring
  have e2 : Y * (500 * (Y + 1) ^ 2 + 100 * (Y + 3)) = 500 * Y ^ 3 + 1100 * Y ^ 2 + 800 * Y := by ring
  have eNV : (NV + 2) * (50 * W + 10 + 1) = 98 * (50 * W) + 98 * 11 := by simp only [NV]; ring
  have q1 : Y ≤ Y ^ 2 := by nlinarith
  have q2 : Y ^ 2 ≤ Y ^ 3 := by nlinarith
  omega

/-! ## The dispatcher's sizes -/

/-- The width constant. -/
def dispG (R n0 c Cs D1 : ℕ) : ℕ := 100 * (Cs + 1) * (D1 + 2) + n0 + 2 * c + 2 * R.size + 100

/-- Width and call bounds `2^((c+1)L)·G` for `L` leading ones. -/
def dispSz (R n0 c Cs D1 : ℕ) : Sz :=
  ⟨dispG R n0 c Cs D1, c + 1, dispG R n0 c Cs D1, c + 1, dispG R n0 c Cs D1, c + 1⟩

/-- The width at `L = n + 4`. -/
def dispX (R n0 c Cs D1 n : ℕ) : ℕ := 2 ^ ((c + 1) * (n + 4)) * dispG R n0 c Cs D1

theorem leadOnes_middle2 (r : AmplifierRequest) : leadOnes (middle2 r) = r.inputArity + 4 :=
  NearCubicGates.Close.CounterMachine.CellTablesProg.leadOnes_rep _ _

theorem dispSz_W (R n0 c Cs D1 : ℕ) (r : AmplifierRequest) :
    (dispSz R n0 c Cs D1).W (leadOnes (middle2 r)) = dispX R n0 c Cs D1 r.inputArity := by
  rw [leadOnes_middle2]; rfl

theorem disp_width (R n0 c Cs D1 n : ℕ) (hc : 1 ≤ c) :
    2 * dispCap Cs D1 c n + n0 + Cs + (44 + R.size) * (2 * n + 5) + 2 * c + n + 10 ≤ dispX R n0 c Cs D1 n ∧
    2 * dispCap Cs D1 c n + 2 * n + 2 ≤ dispX R n0 c Cs D1 n ∧
    55 * (dispCap Cs D1 c n + n + 1) ≤ dispX R n0 c Cs D1 n := by
  set Q := 2 ^ (n + 4) with hQ
  set P := Q ^ c with hP
  set G := dispG R n0 c Cs D1 with hG
  have hQn : n + 5 ≤ Q := by have := Nat.lt_two_pow_self (n := n + 4); omega
  have h3 : 2 ^ (n + 3) ≤ Q := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hnc : n ^ c ≤ P := Nat.pow_le_pow_left (by omega) c
  have hQP : Q ≤ P := Nat.le_self_pow (by omega) Q
  have hX : dispX R n0 c Cs D1 n = G * (P * Q) := by
    unfold dispX
    rw [show (c + 1) * (n + 4) = (n + 4) * c + (n + 4) by ring, pow_add, pow_mul]
    ring
  set U := P * Q with hU
  have hPU : P ≤ U := Nat.le_mul_of_pos_right P (by omega)
  have hQU : Q ≤ U := Nat.le_mul_of_pos_left Q (by omega)
  set K := Cs * (D1 + 2) with hK
  have hcap : dispCap Cs D1 c n ≤ K * U := by
    unfold dispCap
    have hD : D1 ≤ D1 * U := Nat.le_mul_of_pos_right D1 (by omega)
    calc Cs * (2 ^ (n + 3) + n ^ c + D1) ≤ Cs * ((D1 + 2) * U) := Nat.mul_le_mul_left Cs (by
          have e : (D1 + 2) * U = D1 * U + 2 * U := by ring
          omega)
      _ = K * U := by rw [hK]; ring
  have eG : 100 * (Cs + 1) * (D1 + 2) = 100 * K + 100 * D1 + 200 := by rw [hK]; ring
  have hGK1 : 55 * K + 55 ≤ G := by rw [hG]; unfold dispG; omega
  have hGK2 : 2 * K + n0 + Cs + 2 * c + 99 + 2 * R.size ≤ G := by
    rw [hG]; unfold dispG
    have : Cs ≤ K := by rw [hK]; exact Nat.le_mul_of_pos_right Cs (by omega)
    omega
  rw [hX]
  have hs : R.size * (2 * n + 5) ≤ 2 * (R.size * U) := by
    calc R.size * (2 * n + 5) ≤ R.size * (2 * U) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (R.size * U) := by ring
  have e44 : (44 + R.size) * (2 * n + 5) = 44 * (2 * n + 5) + R.size * (2 * n + 5) := by ring
  have hn0U : n0 ≤ n0 * U := Nat.le_mul_of_pos_right n0 (by omega)
  have hCsU : Cs ≤ Cs * U := Nat.le_mul_of_pos_right Cs (by omega)
  have hcU : c ≤ c * U := Nat.le_mul_of_pos_right c (by omega)
  have hGU1 : (2 * K + n0 + Cs + 2 * c + 99 + 2 * R.size) * U ≤ G * U := Nat.mul_le_mul_right U hGK2
  have hGU2 : (55 * K + 55) * U ≤ G * U := Nat.mul_le_mul_right U hGK1
  have e3 : (2 * K + n0 + Cs + 2 * c + 99 + 2 * R.size) * U =
      2 * (K * U) + n0 * U + Cs * U + 2 * (c * U) + 99 * U + 2 * (R.size * U) := by ring
  have e4 : (55 * K + 55) * U = 55 * (K * U) + 55 * U := by ring
  refine ⟨by omega, by omega, by omega⟩

/-! ## The compiled dispatcher -/

/-- The cell-step bound of the dispatcher. -/
noncomputable def dispN (R A a c : ℕ) (hc : 1 ≤ c) (S : ℕ → ℕ) (Cs n : ℕ) : ℕ :=
  preCost (ampOnset A a) c Cs (smallSum S (ampOnset A a))
    (dispX R (ampOnset A a) c Cs (smallSum S (ampOnset A a)) n)
    (dispX R (ampOnset A a) c Cs (smallSum S (ampOnset A a)) n)
    (dispX R (ampOnset A a) c Cs (smallSum S (ampOnset A a)) n) n + branchCost R (ampOnset A a) c hc S n

/-- **The dispatcher as an ordinary machine** (callee: X8's capped time constructor). -/
noncomputable def dispWF (p : Program) (R A a c : ℕ) (hc : 1 ≤ c) (S : ℕ → ℕ) (Cs : ℕ) (hCs : 0 < Cs)
    (hS : ∀ n, ∃ receipt, run p.machine (Cs * (S n + 1)) (p.inputTapes (List.replicate n true)) = some receipt ∧
      receipt.final.tapes p.outputTape = (S n).bits) :
    WordFunction AmplifierRequest middle2 (truthTableWord (ampG R A a c hc S))
      (fun r => langBudget (capCallee p) (dispSz R (ampOnset A a) c Cs (smallSum S (ampOnset A a))) NV 0 (middle2 r)
        (dispN R A a c hc S Cs r.inputArity)) :=
  wordFunction_of_lang middle2 (truthTableWord (ampG R A a c hc S)) (capCallee p)
    (dispSz R (ampOnset A a) c Cs (smallSum S (ampOnset A a)))
    (dispP R (ampOnset A a) c Cs (smallSum S (ampOnset A a))) (fun r => dispN R A a c hc S Cs r.inputArity)
    (fun r => by
      set z := dispSz R (ampOnset A a) c Cs (smallSum S (ampOnset A a)) with hz
      have hWX : z.W (leadOnes (middle2 r)) = dispX R (ampOnset A a) c Cs (smallSum S (ampOnset A a)) r.inputArity :=
        dispSz_W R (ampOnset A a) c Cs (smallSum S (ampOnset A a)) r
      have hL : z.Lk (leadOnes (middle2 r)) = dispX R (ampOnset A a) c Cs (smallSum S (ampOnset A a)) r.inputArity :=
        hWX
      have hB : z.Bk (leadOnes (middle2 r)) = dispX R (ampOnset A a) c Cs (smallSum S (ampOnset A a)) r.inputArity :=
        hWX
      obtain ⟨w1, w2, w3⟩ := disp_width R (ampOnset A a) c Cs (smallSum S (ampOnset A a)) r.inputArity hc
      obtain ⟨b, m, e, ho, hm⟩ := dispP_run (z.W (leadOnes (middle2 r))) (z.Lk (leadOnes (middle2 r)))
        (z.Bk (leadOnes (middle2 r))) (middle2 r) p R A a c hc S Cs hCs hS r rfl
        (by rw [hWX]; exact w1) (by rw [hL]; exact w2) (by rw [hB]; exact w3) (by rw [hB, hWX])
      refine ⟨b, m, e, ho, ?_⟩
      simp only [hWX, hL, hB] at hm
      exact hm)
    (fun r => by
      rw [dispSz_W]; unfold dispX dispG
      exact Nat.one_le_iff_ne_zero.mpr (by positivity))

/-! ## The bounds from the onset -/

/-- The exponent `F` with `Q^F` dominating every term (`Q = 2^(n+4)`). -/
def dispF (R c : ℕ) : ℕ := c + 1 + 12 * (44 + R.size) + 2

theorem pow_le_dispZ (R c n j : ℕ) (hj : j ≤ dispF R c) : (2 ^ (n + 4)) ^ j ≤ (2 ^ (n + 4)) ^ dispF R c :=
  Nat.pow_le_pow_right (Nat.two_pow_pos _) hj

theorem parCost_le (n : ℕ) : parCost (n + 1) ≤ 116 * (2 ^ (n + 4)) ^ 2 := by
  set Q := 2 ^ (n + 4) with hQ
  have hQn : n + 5 ≤ Q := by have := Nat.lt_two_pow_self (n := n + 4); omega
  have hp : 2 ^ (n + 1) ≤ Q := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hs : (n + 1).size ≤ n + 1 := size_le_self _
  unfold parCost hadCost
  have h1 : 2 ^ (n + 1) * ((n + 1) * (30 + 2) + 20 + 5 + 2) ≤ Q * (32 * Q + 27) := Nat.mul_le_mul hp (by omega)
  have e : Q * (32 * Q + 27) = 32 * Q ^ 2 + 27 * Q := by ring
  have hQ2 : Q ≤ Q ^ 2 := Nat.le_self_pow (by norm_num) Q
  omega

theorem restCost_le (R n k : ℕ) (hk : k ≤ n + 3) :
    restCost R n k ≤ 640000 * (2 ^ (n + 4)) ^ (12 * (44 + R.size)) + 2 * R.size := by
  have h1 := encCost_le R n k 0 (Nat.zero_le _)
  have h2 : restCost R n k ≤ encCost R n k 0 := by unfold encCost; omega
  have hl := arity_le R n k
  have hQ : encQ R n k ≤ 2 * (2 ^ (n + 4)) ^ (2 * (44 + R.size)) := by
    unfold encQ
    rw [← pow_mul, pow_succ, Nat.mul_comm (2 ^ _) 2]
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_right (by norm_num)
    have : (44 + R.size) * (n + k + 1) ≤ (44 + R.size) * (2 * (n + 4)) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  have key : ∀ Q m : ℕ, (2 * Q ^ (2 * m)) ^ 6 = 64 * Q ^ (12 * m) := by
    intro Q m; rw [mul_pow, ← pow_mul]; ring_nf
  have h6 : encQ R n k ^ 6 ≤ 64 * (2 ^ (n + 4)) ^ (12 * (44 + R.size)) := by
    calc encQ R n k ^ 6 ≤ (2 * (2 ^ (n + 4)) ^ (2 * (44 + R.size))) ^ 6 := Nat.pow_le_pow_left hQ 6
      _ = 64 * (2 ^ (n + 4)) ^ (12 * (44 + R.size)) := key _ _
  omega

/-- The constant `H` with every dispatcher size parameter at most `H·Q^F` from the onset. -/
def dispH (R n0 c Cs D1 T : ℕ) : ℕ :=
  26 * dispG R n0 c Cs D1 + 10 ^ 6 + 2 * (n0 + c + D1 + Cs) + 15 * c + 2 * R.size + T + 1000

theorem dispN_le (R A a c : ℕ) (hc : 1 ≤ c) (S : ℕ → ℕ) (Cs n T : ℕ) (hn : ampOnset A a ≤ n) :
    dispN R A a c hc S Cs n ≤
      dispH R (ampOnset A a) c Cs (smallSum S (ampOnset A a)) T * (2 ^ (n + 4)) ^ dispF R c := by
  set n0 := ampOnset A a with hn0
  set D1 := smallSum S n0 with hD1
  set G := dispG R n0 c Cs D1 with hG
  set Q := 2 ^ (n + 4) with hQ
  set Z := Q ^ dispF R c with hZ
  have hQn : n + 5 ≤ Q := by have := Nat.lt_two_pow_self (n := n + 4); omega
  have hQZ : Q ≤ Z := by
    have := pow_le_dispZ R c n 1 (by unfold dispF; omega); rwa [pow_one] at this
  have hQ2 : Q ^ 2 ≤ Z := pow_le_dispZ R c n 2 (by unfold dispF; omega)
  have hQ12 : Q ^ (12 * (44 + R.size)) ≤ Z := pow_le_dispZ R c n _ (by unfold dispF; omega)
  have hX : dispX R n0 c Cs D1 n ≤ G * Z := by
    unfold dispX
    rw [Nat.mul_comm]
    apply Nat.mul_le_mul_left
    rw [Nat.mul_comm (c + 1) (n + 4), pow_mul, ← hQ]
    exact pow_le_dispZ R c n _ (by unfold dispF; omega)
  obtain ⟨-, -, w3⟩ := disp_width R n0 c Cs D1 n hc
  set X := dispX R n0 c Cs D1 n with hXd
  have hsz := size_le_self n
  have hb : branchCost R n0 c hc S n ≤ 20 + 116 * Q ^ 2 + (c * 5 + (n + 3) * 7 +
      (640000 * Q ^ (12 * (44 + R.size)) + 2 * R.size) + 30) := by
    unfold branchCost
    rw [if_neg (by omega)]
    have hp := parCost_le n
    rw [← hQ] at hp
    split_ifs with h3
    · obtain ⟨-, hk⟩ := dyadicExp_le c (S n) n hc h3
      have := restCost_le R n _ hk
      rw [← hQ] at this
      omega
    · omega
  have hZ1 : 1 ≤ Z := le_trans (by omega) hQZ
  have hcZ : c ≤ c * Z := Nat.le_mul_of_pos_right c hZ1
  have hRZ : R.size ≤ R.size * Z := Nat.le_mul_of_pos_right _ hZ1
  have hconst : n0 + c + D1 + Cs ≤ (n0 + c + D1 + Cs) * Z := Nat.le_mul_of_pos_right _ hZ1
  unfold dispN
  rw [← hn0, ← hD1, ← hXd]
  unfold preCost capCost dispH
  rw [← hG]
  have e : (26 * G + 10 ^ 6 + 2 * (n0 + c + D1 + Cs) + 15 * c + 2 * R.size + T + 1000) * Z =
      26 * (G * Z) + 10 ^ 6 * Z + 2 * ((n0 + c + D1 + Cs) * Z) + 15 * (c * Z) + 2 * (R.size * Z) + T * Z +
        1000 * Z := by ring
  have hT : 0 ≤ T * Z := Nat.zero_le _
  omega

/-! ## The whole machine and its budget -/

/-- **A05's machine**: prefix, widening, dispatcher. -/
noncomputable def ampMachine (p : Program) (R A a c : ℕ) (hc : 1 ≤ c) (S : ℕ → ℕ) (Cs : ℕ) (hCs : 0 < Cs)
    (hS : ∀ n, ∃ receipt, run p.machine (Cs * (S n + 1)) (p.inputTapes (List.replicate n true)) = some receipt ∧
      receipt.final.tapes p.outputTape = (S n).bits) :=
  Code.composeFramed prep1WF (Code.composeFramed unaryWF (dispWF p R A a c hc S Cs hCs hS))

theorem amplifierInput_le (n : ℕ) (f : BoolFunction n) : (amplifierInput ⟨n, f⟩).length + n + 5 ≤ 2 ^ (n + 4) := by
  rw [amplifierInput_length']
  simp only
  have h1 := size_le_self n
  have h2 := Nat.lt_two_pow_self (n := n)
  have h3 : 2 ^ (n + 4) = 16 * 2 ^ n := by rw [pow_add]; ring
  omega

theorem unary_budget_le (n : ℕ) (f : BoolFunction n) :
    langBudget Code.Parsing.copyCallee unarySz NV 0 (middle1 ⟨n, f⟩) (unaryCost n n.size) ≤
      20000 * ((TSK Code.Parsing.copyCallee + 300) * 2 ^ (n + 4)) ^ 3 := by
  set Q := 2 ^ (n + 4) with hQ
  have hai := amplifierInput_le n f
  have hsz := size_le_self n
  have hpn : 2 ^ n ≤ Q := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hps : 2 ^ n.size ≤ Q := le_trans (Nat.pow_le_pow_right (by norm_num) hsz) hpn
  have hlead : leadOnes (middle1 ⟨n, f⟩) = n.size := NearCubicGates.Close.CounterMachine.CellTablesProg.leadOnes_rep _ _
  set T0 := TSK Code.Parsing.copyCallee
  have hQY : Q ≤ (T0 + 300) * Q := Nat.le_mul_of_pos_left Q (by omega)
  have e300 : (T0 + 300) * Q = T0 * Q + 300 * Q := by ring
  have hQ1 : 1 ≤ Q := Nat.one_le_two_pow
  have hTQ : T0 ≤ T0 * Q := Nat.le_mul_of_pos_right T0 hQ1
  apply langBudget_le_cube
  · omega
  · rw [hlead]; omega
  · rw [hlead]; simp only [unarySz, Sz.W, one_mul]; omega
  · simp [unarySz, Sz.Lk]
  · simp [unarySz, Sz.Bk]
  · simp only [unarySz]; omega
  · omega
  · unfold unaryCost; omega
  · simp only [middle1, List.length_append, List.length_replicate, List.length_cons]; omega

/-- The full budget is at most `2^(e·n)` from the onset. -/
theorem ampMachine_budget (p : Program) (R A a c : ℕ) (hc : 1 ≤ c) (S : ℕ → ℕ) (Cs : ℕ) (n : ℕ) (f : BoolFunction n)
    (hn : ampOnset A a ≤ n) (H : ℕ) (hHd : H = dispH R (ampOnset A a) c Cs (smallSum S (ampOnset A a))
      (TSK (capCallee p) + TSK Code.Parsing.copyCallee + 3 * (c + 1) + 300)) :
    (2 * (2 * prepCost (amplifierInput ⟨n, f⟩).length + 2) + 2) + 1 +
      (2 * ((2 * langBudget Code.Parsing.copyCallee unarySz NV 0 (middle1 ⟨n, f⟩) (unaryCost n n.size) + 2) + 1 +
        (2 * langBudget (capCallee p) (dispSz R (ampOnset A a) c Cs (smallSum S (ampOnset A a))) NV 0 (middle2 ⟨n, f⟩)
          (dispN R A a c hc S Cs n) + 2)) + 2) ≤
      2 ^ ((200000 * H ^ 3 + 15 * dispF R c) * n) := by
  set n0 := ampOnset A a with hn0
  set D1 := smallSum S n0 with hD1
  set G := dispG R n0 c Cs D1 with hG
  set Q := 2 ^ (n + 4) with hQ
  set F := dispF R c with hF
  set Z := Q ^ F with hZ
  set Y := H * Z with hY
  have hQ1 : 1 ≤ Q := Nat.one_le_two_pow
  have hQZ : Q ≤ Z := by
    have := pow_le_dispZ R c n 1 (by unfold dispF; omega); rwa [pow_one] at this
  have hZ1 : 1 ≤ Z := le_trans hQ1 hQZ
  have hH : 26 * G + 3 * (c + 1) + TSK (capCallee p) + TSK Code.Parsing.copyCallee + 300 + 10 ^ 6 ≤ H := by
    rw [hHd]; unfold dispH; rw [← hG]; omega
  have hZY : Z ≤ Y := Nat.le_mul_of_pos_left Z (by omega)
  have hY1 : 1 ≤ Y := le_trans hZ1 hZY
  have hai := amplifierInput_le n f
  -- the dispatcher
  have hX : dispX R n0 c Cs D1 n ≤ G * Z := by
    unfold dispX
    rw [Nat.mul_comm]
    apply Nat.mul_le_mul_left
    rw [Nat.mul_comm (c + 1) (n + 4), pow_mul, ← hQ]
    exact pow_le_dispZ R c n _ (by unfold dispF; omega)
  have hGZ : G * Z ≤ Y := Nat.mul_le_mul_right Z (by omega)
  have hWX : (dispSz R n0 c Cs D1).W (leadOnes (middle2 ⟨n, f⟩)) = dispX R n0 c Cs D1 n := dispSz_W R n0 c Cs D1 ⟨n, f⟩
  have hL : (dispSz R n0 c Cs D1).Lk (leadOnes (middle2 ⟨n, f⟩)) = dispX R n0 c Cs D1 n := hWX
  have hB : (dispSz R n0 c Cs D1).Bk (leadOnes (middle2 ⟨n, f⟩)) = dispX R n0 c Cs D1 n := hWX
  have hN := dispN_le R A a c hc S Cs n (TSK (capCallee p) + TSK Code.Parsing.copyCallee + 3 * (c + 1) + 300) hn
  rw [← hHd, ← hQ, ← hF, ← hZ, ← hY] at hN
  have hdisp : langBudget (capCallee p) (dispSz R n0 c Cs D1) NV 0 (middle2 ⟨n, f⟩) (dispN R A a c hc S Cs n) ≤
      20000 * Y ^ 3 := by
    apply langBudget_le_cube
    · exact hY1
    · rw [leadOnes_middle2]; simp only; omega
    · rw [hWX]; omega
    · rw [hL]; omega
    · rw [hB]; omega
    · simp only [dispSz]
      have : 3 * G + 3 * (c + 1) ≤ H * 1 := by omega
      have := Nat.mul_le_mul_left H hZ1
      omega
    · have := Nat.mul_le_mul_left H hZ1; omega
    · exact hN
    · simp only [middle2, List.length_append, List.length_replicate, List.length_cons]
      have := Nat.mul_le_mul_left H hQZ
      have : Q ≤ H * Q := Nat.le_mul_of_pos_left Q (by omega)
      omega
  -- the widening stage
  have hun := unary_budget_le n f
  have hYu : (TSK Code.Parsing.copyCallee + 300) * Q ≤ Y :=
    Nat.mul_le_mul (by omega) hQZ
  have hun' : langBudget Code.Parsing.copyCallee unarySz NV 0 (middle1 ⟨n, f⟩) (unaryCost n n.size) ≤ 20000 * Y ^ 3 :=
    le_trans hun (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hYu 3))
  -- the prefix stage
  have hpre : 2 * prepCost (amplifierInput ⟨n, f⟩).length + 2 ≤ 1000 * Y ^ 3 := by
    unfold prepCost
    have : Q ≤ Y ^ 3 := le_trans (le_trans hQZ hZY) (Nat.le_self_pow (by norm_num) Y)
    omega
  have htot : (2 * (2 * prepCost (amplifierInput ⟨n, f⟩).length + 2) + 2) + 1 +
      (2 * ((2 * langBudget Code.Parsing.copyCallee unarySz NV 0 (middle1 ⟨n, f⟩) (unaryCost n n.size) + 2) + 1 +
        (2 * langBudget (capCallee p) (dispSz R n0 c Cs D1) NV 0 (middle2 ⟨n, f⟩) (dispN R A a c hc S Cs n) + 2)) + 2) ≤
      200000 * Y ^ 3 := by
    have : 1 ≤ Y ^ 3 := Nat.one_le_pow _ _ hY1
    omega
  refine le_trans htot ?_
  -- `200000·(H·Q^F)^3 ≤ 2^((200000 H^3 + 15 F) n)` for `n ≥ 1`
  have hn1 : 1 ≤ n := by unfold ampOnset at hn0; omega
  have hY3 : Y ^ 3 = H ^ 3 * 2 ^ (3 * F * (n + 4)) := by
    rw [hY, hZ, hQ, mul_pow, ← pow_mul, ← pow_mul]; ring_nf
  rw [hY3]
  have hc1 : 200000 * H ^ 3 ≤ 2 ^ (200000 * H ^ 3 * n) :=
    le_trans Nat.lt_two_pow_self.le (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ hn1))
  have hc2 : 2 ^ (3 * F * (n + 4)) ≤ 2 ^ (15 * F * n) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  calc 200000 * (H ^ 3 * 2 ^ (3 * F * (n + 4))) = (200000 * H ^ 3) * 2 ^ (3 * F * (n + 4)) := by ring
    _ ≤ 2 ^ (200000 * H ^ 3 * n) * 2 ^ (15 * F * n) := Nat.mul_le_mul hc1 hc2
    _ = 2 ^ ((200000 * H ^ 3 + 15 * F) * n) := by rw [← pow_add]; ring_nf

/-! ## A05 -/

/-- **A05 (`app:sources`, "Full-range amplification interface")**: for every time-constructible `S`, the amplifier's truth table is computed by one
ordinary machine within `2^(e·n)` steps from the onset `n0`. -/
theorem constructionObligation : ConstructionObligation := by
  intro R A a c hc S hTC
  obtain ⟨Cs, hCs, ⟨F⟩⟩ := hTC
  have hS : ∀ n, ∃ receipt, run F.program.machine (Cs * (S n + 1))
      (F.program.inputTapes (List.replicate n true)) = some receipt ∧
      receipt.final.tapes F.program.outputTape = (S n).bits := F.realizes
  exact ⟨{ budget := _
           algorithm := ampMachine F.program R A a c hc S Cs hCs hS
           timeExponent := 200000 * dispH R (ampOnset A a) c Cs (smallSum S (ampOnset A a))
              (TSK (capCallee F.program) + TSK Code.Parsing.copyCallee + 3 * (c + 1) + 300) ^ 3 + 15 * dispF R c
           timeOnset := ampOnset A a
           exponentialTime := fun r hr => by
             obtain ⟨n, f⟩ := r
             exact ampMachine_budget F.program R A a c hc S Cs n f hr _ rfl }⟩

end NearCubicGates.Adapters.Amplification.Enc
