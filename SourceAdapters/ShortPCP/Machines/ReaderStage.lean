import SourceAdapters.ShortPCP.Machines.ReaderCall

/-!
# Single-run time, stage 3 (reader): `Time.ReaderStage`, proved

proof of `thm:short-pcp-ours` (Step 4): "consider the computation of V1 … its proof bits are read at addresses below L_π, written
with ℓ bits … replace each read of a proof bit by an oracle gate on the ℓ address bits"; proof of `thm:short-pcp-ours`, Step 2, "The instance": "The
queries of V0 are computed from the random string alone", so all addresses are listed before any is read
(`Time.readerWord`). The reader is the coroutine (`Machines/Coroutine.lean`, `coProgram`) of the re-entrant WMX
program `readerW` (`Machines/ReaderCall.lean`): call `k` answers the pending entry `k − 1` from the answer cell and
asks entry `k` (its address `frame (binary L a)` on the query stream); the last call copies the word, every entry
answered, to the output stream. `reader_coRuns` lists the calls (`CoRuns`), `readerStage` is the stage, within
`300·(|readerWord| + 1)²` steps.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.Machines.ReaderRun

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Adapters.ShortPCP.Machines.Reader NearCubicGates.Adapters.ShortPCP.Machines
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length low_bit)
open StablePartition.Workspace (overlay)

/-! ## Words -/

/-- Unasked entries. -/
def unW (L : ℕ) (todo : List ℕ) : List Bool := (todo.map fun a => entry L a true false false).flatten

theorem unW_length (L : ℕ) (todo : List ℕ) : (unW L todo).length = todo.length * (2 * L + 5) := by
  induction todo with
  | nil => simp [unW]
  | cons x todo ih => simp [unW] at ih ⊢; rw [ih, entry_length]; ring

/-- An answered entry, as data. -/
def ansd (o : ℕ → Bool) (d : ℕ) : ℕ × Bool × Bool := (d, false, o d)

theorem procW_answer (L : ℕ) (o : ℕ → Bool) (an : List Bool) (done : List ℕ) (a : ℕ) (h : readTapeBit an 0 = o a) :
    procW L an (done.map (ansd o) ++ [(a, true, false)]) = oldW L ((done ++ [a]).map (ansd o)) := by
  simp [procW, oldW, ansd, h, Function.comp_def]

theorem oldW_pending (L : ℕ) (o : ℕ → Bool) (done : List ℕ) (a : ℕ) :
    oldW L (done.map (ansd o) ++ [(a, true, false)]) = oldW L (done.map (ansd o)) ++ entry L a false true false := by
  simp [oldW]

theorem readerWord_pre (s L : ℕ) (xs : List ℕ) (rest : List Bool) :
    Time.readerWord s L xs rest = pre s ++ oldW L [] ++ (unW L xs ++ false :: rest) := by
  rw [readerWord_eq]
  simp [pre, oldW, unW]

theorem readWord_pre (s L : ℕ) (o : ℕ → Bool) (xs : List ℕ) (rest : List Bool) :
    Time.readWord s L xs (xs.map o) rest = pre s ++ oldW L (xs.map (ansd o)) ++ false :: rest := by
  rw [readWord_eq]
  have hz : ∀ ys : List ℕ, List.zipWith (fun a b => entry L a false false b) ys (ys.map o) =
      ys.map (fun a => entry L a false false (o a)) := by
    intro ys; induction ys with
    | nil => rfl
    | cons y ys ih => simp [ih]
  rw [hz]
  simp [pre, oldW, ansd, Function.comp_def]

/-! ## States -/

theorem rest_sc (u qs an fl : List Bool) : Rest (sc u 0 qs 0 an fl 0) :=
  ⟨fun i => by fin_cases i <;> rfl, fun r => by fin_cases r <;> rfl⟩

theorem rest_finSt (u qs an fl : List Bool) : Rest (finSt u qs an fl) :=
  ⟨fun i => by fin_cases i <;> rfl, fun r => by fin_cases r <;> rfl⟩

theorem sc_setsAN (u : List Bool) (h : ℕ) (qs : List Bool) (hq : ℕ) (an fl : List Bool) (g : ℕ) (x : List Bool) :
    (sc u h qs hq an fl g).sets 3 x = sc u h qs hq x fl g := by
  apply WState.eq
  · rfl
  · funext i; fin_cases i <;> simp [sc]
  · rfl
  · rfl

theorem inputState_eq (u : List Bool) : (inputState u : WState 4 4) = sc u 0 [] 0 [] [] 0 := by
  apply WState.eq
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem bitsValue_binary : ∀ (L n : ℕ), n < 2 ^ L → CanonicalBinary.bitsValue (binary L n) = n
  | 0, n, h => by simp at h; subst h; rfl
  | L + 1, n, h => by
    rw [pow_succ] at h
    simp only [binary, CanonicalBinary.bitsValue]
    rw [bitsValue_binary L (n / 2) (by omega), low_bit n]
    omega

/-! ## The calls -/

variable (cap : ℕ)

/-- **The calls after the first ask**, by induction on the entries not yet asked: the state holds the word with
the entries `done` answered, `a` pending (its answer in `AN[0]`), `todo` not asked. -/
theorem coRuns_after (o : ℕ → Bool) (s L : ℕ) (xs : List ℕ) (rest : List Bool) (N : ℕ)
    (hN : N = s + 1 + xs.length * (2 * L + 5) + 1 + rest.length) (hcap : 2 * N + 10 ≤ cap) :
    ∀ (todo done : List ℕ) (a : ℕ) (qs an fl : List Bool), done ++ a :: todo = xs → readTapeBit an 0 = o a →
      (∀ b ∈ todo, b < 2 ^ L) →
      ∃ c, c ≤ (todo.length + 1) * (200 * (N + 1) + 2 * N + 10) ∧
        CoRuns cap o readerW 2 3 4 1 (Time.readWord s L xs (xs.map o) rest)
          (sc (pre s ++ oldW L (done.map (ansd o) ++ [(a, true, false)]) ++ (unW L todo ++ false :: rest))
            0 qs 0 an fl 0) c
  | [], done, a, qs, an, fl, hxs, han, _ => by
    have hlen : (done.map (ansd o) ++ [(a, true, false)]).length = xs.length := by rw [← hxs]; simp
    have e := call_fin cap s L (done.map (ansd o) ++ [(a, true, false)]) rest qs an fl
      (by rw [hlen]; omega)
    rw [procW_answer L o an done a han, hxs, hlen] at e
    rw [show unW L [] ++ false :: rest = false :: rest from rfl]
    refine ⟨_, ?_, CoRuns.stop (rest_sc _ _ _ _) e (rest_finSt _ _ _ _) (read_write_zero _ _) ?_⟩
    · simp only [List.length_nil]; omega
    · show frame _ = frame _
      rw [readWord_pre]
  | b :: todo, done, a, qs, an, fl, hxs, han, hb => by
    set olds := done.map (ansd o) ++ [(a, true, false)]
    have hlen : olds.length = done.length + 1 := by simp [olds]
    have hx : xs.length = done.length + 2 + todo.length := by rw [← hxs]; simp; omega
    have hX : xs.length * (2 * L + 5) = olds.length * (2 * L + 5) + (2 * L + 5) + todo.length * (2 * L + 5) := by
      rw [hx, hlen]; ring
    have hL : 2 * L + 5 ≤ xs.length * (2 * L + 5) := Nat.le_mul_of_pos_left _ (by omega)
    have hw : pre s ++ oldW L olds ++ (unW L (b :: todo) ++ false :: rest) =
        pre s ++ oldW L olds ++ entry L b true false false ++ (unW L todo ++ false :: rest) := by
      simp [unW]
    have e := call_ask cap s L b olds (unW L todo ++ false :: rest) qs an fl
      (by simp [unW_length]; omega)
    rw [← hw] at e
    obtain ⟨c2, hc2, h2⟩ := coRuns_after o s L xs rest N hN hcap todo (done ++ [a]) b
      (overlay (frame (binary L b)) qs) (writeTapeBit an 0 (o b)) (writeTapeBit fl 0 true)
      (by rw [← hxs]; simp) (read_write_zero _ _) (fun x hx => hb x (List.mem_cons_of_mem _ hx))
    have hnext : (sc (pre s ++ procW L an olds ++ entry L b false true false ++ (unW L todo ++ false :: rest)) 0
        (overlay (frame (binary L b)) qs) 0 an (writeTapeBit fl 0 true) 0).sets 3
        (writeTapeBit an 0 (o (CanonicalBinary.bitsValue (binary L b)))) =
        sc (pre s ++ oldW L ((done ++ [a]).map (ansd o) ++ [(b, true, false)]) ++ (unW L todo ++ false :: rest)) 0
          (overlay (frame (binary L b)) qs) 0 (writeTapeBit an 0 (o b)) (writeTapeBit fl 0 true) 0 := by
      rw [sc_setsAN, bitsValue_binary L b (hb b (by simp)), procW_answer L o an done a han, oldW_pending]
      simp only [List.append_assoc]
    rw [← hnext] at h2
    refine ⟨_, ?_, CoRuns.ask (binary L b) _ (rest_sc _ _ _ _) e (rest_sc _ _ _ _) (read_write_zero _ _) rfl h2⟩
    have hF : (frame (binary L b)).length = 2 * L + 1 := by simp [RepairOrdinary.frame_length]
    rw [hF]
    have hm : ((b :: todo).length + 1) * (200 * (N + 1) + 2 * N + 10) =
        (200 * (N + 1) + 2 * N + 10) + (todo.length + 1) * (200 * (N + 1) + 2 * N + 10) := by simp; ring
    rw [hm]
    simp only [List.length_append, unW_length, List.length_cons]
    omega

/-- **All calls of the reader**, from the framed reader word. -/
theorem reader_coRuns (o : ℕ → Bool) (s L : ℕ) (xs : List ℕ) (rest : List Bool) (hxs : ∀ a ∈ xs, a < 2 ^ L)
    (N : ℕ) (hN : N = s + 1 + xs.length * (2 * L + 5) + 1 + rest.length) (hcap : 2 * N + 10 ≤ cap) :
    ∃ c, c ≤ (xs.length + 1) * (200 * (N + 1) + 2 * N + 10) ∧
      CoRuns cap o readerW 2 3 4 1 (Time.readWord s L xs (xs.map o) rest)
        (inputState (Time.readerWord s L xs rest)) c := by
  rw [inputState_eq, readerWord_pre]
  cases xs with
  | nil =>
    have e := call_fin cap s L [] rest [] [] [] (by simp at hN ⊢; omega)
    rw [show unW L [] ++ false :: rest = false :: rest from rfl]
    refine ⟨_, ?_, CoRuns.stop (rest_sc _ _ _ _) e (rest_finSt _ _ _ _) (read_write_zero _ _) ?_⟩
    · simp at hN ⊢; omega
    · show frame _ = frame _
      rw [readWord_pre]
      simp [procW, oldW]
  | cons b todo =>
    have hL : 2 * L + 5 ≤ (b :: todo).length * (2 * L + 5) := Nat.le_mul_of_pos_left _ (by simp)
    have hX : (b :: todo).length * (2 * L + 5) = (2 * L + 5) + todo.length * (2 * L + 5) := by simp; ring
    have hw : pre s ++ oldW L [] ++ (unW L (b :: todo) ++ false :: rest) =
        pre s ++ oldW L [] ++ entry L b true false false ++ (unW L todo ++ false :: rest) := by
      simp [unW]
    have e := call_ask cap s L b [] (unW L todo ++ false :: rest) [] [] [] (by simp [unW_length]; omega)
    rw [← hw] at e
    obtain ⟨c2, hc2, h2⟩ := coRuns_after cap o s L (b :: todo) rest N hN hcap todo [] b
      (overlay (frame (binary L b)) []) (writeTapeBit [] 0 (o b)) (writeTapeBit [] 0 true) rfl (read_write_zero _ _)
      (fun x hx => hxs x (List.mem_cons_of_mem _ hx))
    have hnext : (sc (pre s ++ procW L [] [] ++ entry L b false true false ++ (unW L todo ++ false :: rest)) 0
        (overlay (frame (binary L b)) []) 0 [] (writeTapeBit [] 0 true) 0).sets 3
        (writeTapeBit [] 0 (o (CanonicalBinary.bitsValue (binary L b)))) =
        sc (pre s ++ oldW L (([] : List ℕ).map (ansd o) ++ [(b, true, false)]) ++ (unW L todo ++ false :: rest)) 0
          (overlay (frame (binary L b)) []) 0 (writeTapeBit [] 0 (o b)) (writeTapeBit [] 0 true) 0 := by
      rw [sc_setsAN, bitsValue_binary L b (hxs b (by simp))]
      simp [procW, oldW]
    rw [← hnext] at h2
    refine ⟨_, ?_, CoRuns.ask (binary L b) _ (rest_sc _ _ _ _) e (rest_sc _ _ _ _) (read_write_zero _ _) rfl h2⟩
    have hF : (frame (binary L b)).length = 2 * L + 1 := by simp [RepairOrdinary.frame_length]
    rw [hF]
    have hm : ((b :: todo).length + 1) * (200 * (N + 1) + 2 * N + 10) =
        (200 * (N + 1) + 2 * N + 10) + (todo.length + 1) * (200 * (N + 1) + 2 * N + 10) := by simp; ring
    rw [hm]
    simp only [List.length_append, unW_length, List.length_cons, List.length_nil] at hN ⊢
    have hX' : (todo.length + 1) * (2 * L + 5) = 2 * L + 5 + todo.length * (2 * L + 5) := by ring
    omega

/-! ## The stage -/

/-- The reader as an oracle program. -/
noncomputable def readerProgram : RepairSource.OrdinaryOracleProgram :=
  coProgram readerW (2 : Fin 5) 3 4 1 (by decide) (by decide)

theorem readerWord_length (s L : ℕ) (xs : List ℕ) (rest : List Bool) :
    (Time.readerWord s L xs rest).length = s + 1 + xs.length * (2 * L + 5) + 1 + rest.length := by
  rw [readerWord_pre]
  simp [pre, oldW, unW_length]
  omega

/-- **Stage 3 of `Time.singleRunTime_of_stages`, proved** (proof of `thm:short-pcp-ours`): every address of the reader word is asked
once, in order, as `frame (binary L a)`, and the output is the read word, within `300·(|readerWord| + 1)²` steps. -/
theorem readerStage : Time.ReaderStage := by
  refine ⟨readerProgram, 300, 2, ?_⟩
  intro o s L xs rest hxs
  set N := (Time.readerWord s L xs rest).length with hNdef
  have hN := readerWord_length s L xs rest
  rw [← hNdef] at hN
  obtain ⟨c, hc, h⟩ := reader_coRuns (2 * N + 10) o s L xs rest hxs N hN le_rfl
  refine Time.runs_mono (coRuns_runs (2 * N + 10) o (by decide) (by decide) h) ?_
  have h1 : xs.length ≤ N := by
    have : xs.length ≤ xs.length * (2 * L + 5) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  calc c ≤ (xs.length + 1) * (200 * (N + 1) + 2 * N + 10) := hc
    _ ≤ (N + 1) * (300 * (N + 1)) := Nat.mul_le_mul (by omega) (by omega)
    _ = 300 * (N + 1) ^ 2 := by ring

end NearCubicGates.Adapters.ShortPCP.Machines.ReaderRun
