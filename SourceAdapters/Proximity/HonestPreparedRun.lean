import SourceAdapters.Proximity.HonestPreparedConfig

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": initialized execution from the paid prepared word
loads the input and schedule, restores the source cursor, and calls the original
honest producer. All stores and fixed parameters required by the row loop are explicit. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.HonestPrepared

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Published.CW19Proximity
open NearCubicGates.Adapters.Joins
open SourceRequests (State Script lengthReg)
open SourceCallee (truthLengthReg)
open QueryStep (boundReg)
open TrimHonest (inputStore inputLength proofStore scheduleStore scheduleLength localBound)

def program (q : ℕ) : Script := .seq (setup q) (.seq readyScript HonestSource.script)
def initialScratch : List (Fin VV) := setupScratch ++ loadScratch ++ HonestSource.scratch

def initialCost {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofSize : SourceCircuit → ℕ) (p : AcceptedSourceInput) (Lk Bk : ℕ) : ℕ :=
  2 * q + 2 * 2 ^ q + 2 * blockVariableBound q + 17 +
    1100 * ((preparedHonestInput V p).length + 1) ^ 2 +
    (15 * (sourceCircuitWord p.1).length + 9 * p.1.arity + Lk + Bk + 9 * proofSize p.1 + 33) + 2

structure Initialized {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofSize : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofSize p.1))
    (p : AcceptedSourceInput) (b : State) : Prop where
  constants : Cst b
  bound : b.env boundReg = q
  truth : b.env truthLengthReg = 2 ^ q
  local_bound : b.env localBound = blockVariableBound q
  source_length : b.env lengthReg = (sourceCircuitWord p.1).length
  input_length : b.env inputLength = p.1.arity
  proof_length : b.env TrimHonest.proofLength = proofSize p.1
  schedule_count : b.env scheduleLength = (trimSortedAddresses (clauseTrimRequest V p.1)).length
  input_ram : b.ram inputStore = (List.ofFn p.2.val).map Bool.toNat
  proof_ram : b.ram proofStore = (List.ofFn (honest p)).map Bool.toNat
  schedule_ram : b.ram scheduleStore = trimSortedAddresses (clauseTrimRequest V p.1)
  input_cursor : b.rc inputStore = p.1.arity
  proof_cursor : b.rc proofStore = proofSize p.1
  schedule_cursor : b.rc scheduleStore = (trimSortedAddresses (clauseTrimRequest V p.1)).length
  cursor : b.ip = (natWord (preparedHonestInput V p).length ++ natWord (sourceCircuitWord p.1).length).length
  out : b.out = []
  kin : b.kin = []
  kout : b.kout = frame (List.ofFn (honest p))
  kc : b.kc = (frame (List.ofFn (honest p))).length
  others : ∀ m, m ≠ inputStore → m ≠ proofStore → m ≠ scheduleStore → b.ram m = [] ∧ b.rc m = 0
  vars : Fr (a0 : State) b initialScratch

variable {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofSize : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofSize p.1))
    (budget : ProofCall V → ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofSize honest) budget)

theorem initial_run (p : AcceptedSourceInput) (Wd Lk Bk : ℕ)
    (hW : (preparedHonestInput V p).length + 3 ≤ Wd)
    (hq : q < 2 ^ Wd) (ht : 2 ^ q < 2 ^ Wd) (hB : blockVariableBound q < 2 ^ Wd)
    (hproof : proofSize p.1 < 2 ^ Wd)
    (hroom : 2 + (sourceCircuitWord p.1).length + p.1.arity ≤ Lk)
    (hbudget : budget (HonestSource.request V p) ≤ Bk) :
    let C := SourceCallee.context V proofSize honest budget P Wd
      (LengthPrefix.wrapped (preparedHonestInput V p)) Lk Bk
    Hs C (program q) (a0 : State) (initialCost V proofSize p Lk Bk)
      (Initialized V proofSize honest p) := by
  dsimp only
  let C := SourceCallee.context V proofSize honest budget P Wd
    (LengthPrefix.wrapped (preparedHonestInput V p)) Lk Bk
  let source := sourceCircuitWord p.1
  let bits := List.ofFn p.2.val
  let records := trimSortedAddresses (clauseTrimRequest V p.1)
  let pre := sourcePrefix source bits records
  let tail := frame bits ++ natWord records.length ++ records.flatMap natWord
  have hw : word source bits records = preparedHonestInput V p := word_prepared V p
  have hshape : LengthPrefix.wrapped (preparedHonestInput V p) = pre ++ sourceCircuitWord p.1 ++ tail := by
    rw [← hw]
    simp only [LengthPrefix.wrapped, pre, sourcePrefix, word, tail, source, List.append_assoc]
  have hTwo : 2 < 2 ^ Wd := by have he := Nat.lt_two_pow_self (n := Wd); omega
  obtain ⟨b, nb, eb, hb, rb⟩ := setup_run C q hTwo hq ht hB
  obtain ⟨c, nc, ec, hc, rc⟩ := ready_run C b rb.constants source bits records
    (by change LengthPrefix.wrapped (preparedHonestInput V p) = _; rw [hw]) rb.ip
    (by rw [rb.ram]) (by rw [rb.rc]) (by rw [rb.ram]) (by rw [rb.rc])
    (by change (word source bits records).length + 3 ≤ Wd; rwa [hw])
  have hiLen : c.env inputLength = p.1.arity := by simpa only [bits, List.length_ofFn] using rc.input_length
  have hiWidth : p.1.arity < 2 ^ Wd := by
    have hh := (word_bounds source bits records).2.1
    simp only [bits, List.length_ofFn, hw] at hh
    have he := Nat.lt_two_pow_self (n := Wd)
    omega
  have call := HonestSource.run V proofSize honest budget P p Wd Lk Bk pre tail c rc.constants
    rc.source_length rc.cursor (rc.kin.trans rb.kin) rc.input_ram hiLen
    (by rw [(rc.others proofStore (by decide) (by decide)).1, rb.ram])
    (by rw [(rc.others proofStore (by decide) (by decide)).2, rb.rc]) hiWidth hproof hroom hbudget
  change Hs (SourceCallee.context V proofSize honest budget P Wd
    (pre ++ sourceCircuitWord p.1 ++ tail) Lk Bk) _ _ _ _ at call
  rw [← hshape] at call
  obtain ⟨d, nd, ed, hd, dm, dlen, dr, di, dip, dout, dkin, dkout, dkc, dc, dother, dcother, df⟩ := call
  refine ⟨d, _, Ex.seq eb (Ex.seq ec ed), ?_, ?_⟩
  · rw [rc.input_cursor] at hd
    simp only [bits, List.length_ofFn] at hd
    rw [hw] at hc
    unfold initialCost
    omega
  refine ⟨dc, ?_, ?_, ?_, ?_, ?_, dlen, ?_, ?_, dm, ?_, di, dr, ?_, ?_,
    dout.trans (rc.out.trans rb.out), dkin, dkout, dkc, ?_, ?_⟩
  · exact (df boundReg (by decide)).trans ((rc.vars boundReg (by decide)).trans rb.bound)
  · exact (df truthLengthReg (by decide)).trans ((rc.vars truthLengthReg (by decide)).trans rb.truth)
  · exact (df localBound (by decide)).trans ((rc.vars localBound (by decide)).trans rb.local_bound)
  · exact (df lengthReg (by decide)).trans rc.source_length
  · exact (df inputLength (by decide)).trans hiLen
  · exact (df scheduleLength (by decide)).trans rc.schedule_count
  · exact (dother inputStore (by decide)).trans rc.input_ram
  · exact (dother scheduleStore (by decide)).trans rc.schedule_ram
  · exact (dcother scheduleStore (by decide) (by decide)).trans rc.schedule_cursor
  · rw [dip]
    simp only [pre, sourcePrefix, hw, source]
  · intro m hmi hmp hms
    rw [dother m hmp, dcother m hmp hmi, (rc.others m hmi hms).1, (rc.others m hmi hms).2,
      rb.ram, rb.rc]
    exact ⟨rfl, rfl⟩
  · exact (rb.vars.weaken (by decide)).trans ((rc.vars.weaken (by decide)).trans (df.weaken (by decide)))

end NearCubicGates.Adapters.Proximity.HonestPrepared
