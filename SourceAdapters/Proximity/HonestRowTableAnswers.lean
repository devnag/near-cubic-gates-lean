import SourceAdapters.Proximity.HonestRowTableData

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": actual source query generation followed by
bounded input/proof lookup, retaining exact finite answer and query stores. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.HonestRowTable

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity
open SourceRequests (State Script lengthReg)
open TrimHonest (queryStore inputStore proofStore inputLength proofLength answerStore rowStore localBound)
open HonestTableCall (truthStore)
open QueryStep (rowReg countReg boundReg)

def answersScript : Script := .seq (SourceCallee.queryStage queryStore) TrimHonest.answerProgram
def answerScratch : List (Fin VV) := SourceCallee.queryScratch ++ TrimHonest.answerLoopTemps

structure Answered {q N : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (S : SourceCircuit) (coins : Fin (2 ^ (V S).randomBits)) (C : Ctx)
    (input : BitInput S.arity) (proof : BitInput N) (a b : State) : Prop where
  constants : Cst b
  count : b.env countReg = (V S).queryCount coins
  query_ram : b.ram queryStore = QueryRows.rowFields (fun i => SourceCallee.addressPair ((V S).query coins i)) q
  query_cursor : b.rc queryStore = 2 * q
  answer_ram : b.ram answerStore = (List.ofFn (TrimHonest.rowAnswers (V S) coins input proof)).map Bool.toNat
  answer_cursor : b.rc answerStore = q
  oracle : TrimHonest.OracleReady C input proof b
  ip : b.ip = a.ip
  out : b.out = a.out
  kin : b.kin = []
  other_store : ∀ m, m ≠ queryStore → m ≠ answerStore → b.ram m = a.ram m
  other_cursor : ∀ m, m ∉ TrimHonest.queryCursors → b.rc m = a.rc m
  vars : Fr a b answerScratch

variable {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofSize : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofSize p.1))
    (budget : ProofCall V → ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofSize honest) budget)

theorem answers_stages (S : SourceCircuit) (coins : Fin (2 ^ (V S).randomBits))
    {N : ℕ} (input : BitInput S.arity) (proof : BitInput N)
    (Wd Lk Bk Λ : ℕ) (pre tail : List Bool) (a : State)
    (ha : Ready (SourceCallee.context V proofSize honest budget P Wd
      (pre ++ sourceCircuitWord S ++ tail) Lk Bk) input proof q (sourceCircuitWord S).length pre.length a)
    (hrow : a.env rowReg = coins.val) (H : Bounds V budget S coins input proof Wd Lk Bk Λ) :
    let C := SourceCallee.context V proofSize honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
    ∃ b c nb nc, Ex C (SourceCallee.queryStage queryStore) a b nb ∧
      Ex C TrimHonest.answerProgram b c nc ∧ nb + nc + 1 ≤
      ((q * (15 * (sourceCircuitWord S).length + Lk + Bk + 30 * Λ + 64) +
        15 * (sourceCircuitWord S).length + Lk + Bk + 20 * Λ + 2 * q + 50) +
        (3 * q + (6 * (S.arity + N) + 21) * q + 8) + 1)
      ∧ Answered V S coins C input proof a c := by
  dsimp only
  let C := SourceCallee.context V proofSize honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
  obtain ⟨b, nb, eb, hb, rb⟩ := SourceCallee.query_stage V proofSize honest budget P S coins Wd Lk Bk Λ
    pre tail queryStore a ha.source.constants H.width_four H.width_bits H.query_width hrow
    ha.source.bound_eq ha.source.source_length ha.source.input_cursor ha.source.kin_nil
    ha.source.query_cursor ha.source.query_length H.row_bits H.count_bits H.query_bits H.address_bits
    H.count_room H.count_budget H.query_room H.query_budget
  have cb := rb.constants ha.source.constants
  have ob : TrimHonest.OracleReady C input proof b := by
    refine ⟨?_, (rb.vars inputLength (by decide)).trans ha.oracle.input_len, ?_, ha.oracle.input_width,
      ?_, (rb.vars proofLength (by decide)).trans ha.oracle.proof_len, ?_, ha.oracle.proof_width⟩
    · rw [rb.ram_eq, Function.update_of_ne (by decide : inputStore ≠ queryStore)]; exact ha.oracle.input_ram
    · rw [rb.cursor_eq, Function.update_of_ne (by decide : inputStore ≠ queryStore)]; exact ha.oracle.input_cursor
    · rw [rb.ram_eq, Function.update_of_ne (by decide : proofStore ≠ queryStore)]; exact ha.oracle.proof_ram
    · rw [rb.cursor_eq, Function.update_of_ne (by decide : proofStore ≠ queryStore)]; exact ha.oracle.proof_cursor
  obtain ⟨c, nc, ec, hc, cm, ca, cq, oc, cf⟩ := TrimHonest.row_answers (C := C) (V S) coins input proof b cb ob
    (by rw [rb.ram_eq, Function.update_self])
    ((rb.vars boundReg (by decide)).trans ha.source.bound_eq)
    (by rw [rb.ram_eq, Function.update_of_ne (by decide : answerStore ≠ queryStore)]; exact ha.answers_length)
    H.query_width
  refine ⟨b, c, nb, nc, eb, ec, ?_, ?_⟩
  · rw [rb.cursor_eq, Function.update_self, Function.update_of_ne (by decide : answerStore ≠ queryStore)] at hc
    have hh := ha.answers_cursor
    omega
  refine ⟨cf.constants cb (by decide), (cf.env countReg (by decide)).trans rb.count_eq,
    ?_, cq, cm, ca, oc, cf.ip.trans rb.ip_eq, cf.out.trans rb.out_eq, cf.kin.trans rb.kin_nil, ?_, ?_, ?_⟩
  · rw [cf.ram queryStore (by decide), rb.ram_eq, Function.update_self]
  · intro m hq ha
    rw [cf.ram m ha, rb.ram_eq, Function.update_of_ne hq]
  · intro m hm
    have hq : m ≠ queryStore := by intro h; apply hm; simp [TrimHonest.queryCursors, h]
    rw [cf.cursor m hm, rb.cursor_eq, Function.update_of_ne hq]
  · exact (rb.vars.weaken (by decide)).trans (cf.env.weaken (by decide))

end NearCubicGates.Adapters.Proximity.HonestRowTable
