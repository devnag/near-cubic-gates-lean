import SourceAdapters.Proximity.HonestRowTableAnswers

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the complete paid row pipeline builds the exact
canonical assignment while preserving accumulated auxiliary and schedule data. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.HonestRowTable

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity
open SourceRequests (State Script lengthReg)
open TrimHonest (queryStore inputStore proofStore inputLength proofLength answerStore rowStore localBound)
open HonestTableCall (truthStore)
open QueryStep (rowReg countReg boundReg)
open SourceCallee (truthLengthReg)

variable {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofSize : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofSize p.1))
    (budget : ProofCall V → ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofSize honest) budget)

theorem run (S : SourceCircuit) (coins : Fin (2 ^ (V S).randomBits))
    {N : ℕ} (input : BitInput S.arity) (proof : BitInput N)
    (Wd Lk Bk Λ : ℕ) (pre tail : List Bool) (a : State)
    (ha : Ready (SourceCallee.context V proofSize honest budget P Wd
      (pre ++ sourceCircuitWord S ++ tail) Lk Bk) input proof q (sourceCircuitWord S).length pre.length a)
    (hrow : a.env rowReg = coins.val) (H : Bounds V budget S coins input proof Wd Lk Bk Λ) :
    let C := SourceCallee.context V proofSize honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
    Hs C (script q) a (cost q S.arity N (sourceCircuitWord S).length Lk Bk Λ)
      (Result V S coins C input proof pre.length a) := by
  dsimp only
  let C := SourceCallee.context V proofSize honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
  obtain ⟨b, c, nb, nc, eb, ec, hc, rc⟩ := answers_stages V proofSize honest budget P S coins
    input proof Wd Lk Bk Λ pre tail a ha hrow H
  obtain ⟨d, nd, ed, hd, rd⟩ := SourceCallee.table_stage V proofSize honest budget P S coins Wd Lk Bk Λ
    pre tail truthStore c rc.constants H.width_four ((rc.vars rowReg (by decide)).trans hrow) rc.count
    ((rc.vars lengthReg (by decide)).trans ha.source.source_length)
    (rc.ip.trans ha.source.input_cursor) rc.kin
    (by rw [rc.other_cursor truthStore (by decide)]; exact ha.source.truth_cursor)
    (by rw [rc.other_store truthStore (by decide) (by decide)]; exact ha.source.truth_size)
    H.row_bits H.decision_room H.decision_budget
  have cd := rd.constants rc.constants
  have fcd : Fr a d (answerScratch ++ DecisionCalls.scratch) :=
    (rc.vars.weaken (by decide)).trans (rd.vars.weaken (by decide))
  have od : TrimHonest.OracleReady C input proof d := by
    refine ⟨?_, (rd.vars inputLength (by decide)).trans rc.oracle.input_len, ?_, rc.oracle.input_width,
      ?_, (rd.vars proofLength (by decide)).trans rc.oracle.proof_len, ?_, rc.oracle.proof_width⟩
    · rw [rd.ram_eq, Function.update_of_ne (by decide : inputStore ≠ truthStore)]; exact rc.oracle.input_ram
    · rw [rd.cursor_eq, Function.update_of_ne (by decide : inputStore ≠ truthStore)]; exact rc.oracle.input_cursor
    · rw [rd.ram_eq, Function.update_of_ne (by decide : proofStore ≠ truthStore)]; exact rc.oracle.proof_ram
    · rw [rd.cursor_eq, Function.update_of_ne (by decide : proofStore ≠ truthStore)]; exact rc.oracle.proof_cursor
  have dtruth : d.ram truthStore = (List.ofFn (predicateTable (rowPredicate (V S) coins))).map Bool.toNat := by
    rw [rd.ram_eq, Function.update_self]
  have danswers : d.ram answerStore = (List.ofFn (TrimHonest.rowAnswers (V S) coins input proof)).map Bool.toNat := by
    rw [rd.ram_eq, Function.update_of_ne (by decide : answerStore ≠ truthStore), rc.answer_ram]
  have drow : (d.ram rowStore).length ≤ blockVariableBound q := by
    rw [rd.ram_eq, Function.update_of_ne (by decide : rowStore ≠ truthStore),
      rc.other_store rowStore (by decide) (by decide)]
    exact ha.row_length
  obtain ⟨f, nf, ef, hf, fm, fr, fkc, ftc, fac, fip, fout, fkin, fkout, cf, fother, fcother, ff⟩ :=
    HonestTableReuse.run V proofSize honest budget P (rowPredicate (V S) coins)
      (TrimHonest.rowAnswers (V S) coins input proof) Wd Lk Bk
      (pre ++ sourceCircuitWord S ++ tail) d cd dtruth danswers
      ((fcd truthLengthReg (by decide)).trans ha.source.truth_length)
      ((fcd boundReg (by decide)).trans ha.source.bound_eq)
      ((fcd localBound (by decide)).trans ha.local_bound) drow rd.kin_nil
      H.truth_width H.query_width H.row_width H.table_room H.table_budget
  have fv : Fr a f scratch := (fcd.weaken (by decide)).trans (ff.weaken (by decide))
  have fo : TrimHonest.OracleReady C input proof f := by
    refine ⟨(fother inputStore (by decide)).trans od.input_ram,
      (ff inputLength (by decide)).trans od.input_len, ?_, od.input_width,
      (fother proofStore (by decide)).trans od.proof_ram,
      (ff proofLength (by decide)).trans od.proof_len, ?_, od.proof_width⟩
    · rw [fcother inputStore (by decide) (by decide) (by decide)]; exact od.input_cursor
    · rw [fcother proofStore (by decide) (by decide) (by decide)]; exact od.proof_cursor
  have fs : SourceCallee.RowState q (sourceCircuitWord S).length pre.length queryStore truthStore f := by
    refine ⟨cf, (fv boundReg (by decide)).trans ha.source.bound_eq,
      (fv truthLengthReg (by decide)).trans ha.source.truth_length,
      (fv lengthReg (by decide)).trans ha.source.source_length,
      fip.trans (rd.ip_eq.trans (rc.ip.trans ha.source.input_cursor)), fkin, ?_, ?_, ?_, ftc.le⟩
    · rw [fother queryStore (by decide), rd.ram_eq,
        Function.update_of_ne (by decide : queryStore ≠ truthStore), rc.query_ram, QueryRows.rowFields_length]
    · rw [fcother queryStore (by decide) (by decide) (by decide), rd.cursor_eq,
        Function.update_of_ne (by decide : queryStore ≠ truthStore), rc.query_cursor]
    · rw [fother truthStore (by decide), dtruth]
      simp only [List.length_map, List.length_ofFn, le_refl]
  refine ⟨f, _, Ex.seq eb (Ex.seq ec (Ex.seq ed ef)), ?_, ?_⟩
  · rw [rd.cursor_eq, Function.update_self, Function.update_of_ne (by decide : answerStore ≠ truthStore),
      Function.update_of_ne (by decide : rowStore ≠ truthStore), rc.answer_cursor,
      rc.other_cursor rowStore (by decide)] at hf
    simp only [List.length_map, List.length_ofFn] at hf
    have hrowc := ha.row_cursor
    unfold cost
    omega
  refine ⟨⟨fs, fo, ?_, fac.le, ?_, fr.le, (fv localBound (by decide)).trans ha.local_bound⟩,
    fm, fr, fout.trans (rd.out_eq.trans rc.out), ?_, ?_, fv⟩
  · rw [fother answerStore (by decide), danswers]
    simp only [List.length_map, List.length_ofFn, le_refl]
  · rw [fm]
    simp only [HonestTableCall.rowWord, List.length_map, List.length_ofFn, le_refl]
  · intro m hm
    have hq : m ≠ queryStore := by intro h; apply hm; simp [stores, h]
    have ht : m ≠ truthStore := by intro h; apply hm; simp [stores, h]
    have ha : m ≠ answerStore := by intro h; apply hm; simp [stores, h]
    have hr : m ≠ rowStore := by intro h; apply hm; simp [stores, h]
    rw [fother m hr, rd.ram_eq, Function.update_of_ne ht, rc.other_store m hq ha]
  · intro m hm
    have ht : m ≠ truthStore := by intro h; apply hm; simp [cursors, h]
    have ha : m ≠ answerStore := by intro h; apply hm; simp [cursors, h]
    have hr : m ≠ rowStore := by intro h; apply hm; simp [cursors, h]
    have hq : m ∉ TrimHonest.queryCursors := by
      intro h
      apply hm
      simpa only [cursors, TrimHonest.queryCursors, List.mem_cons, List.not_mem_nil, or_false] using
        (show m = queryStore ∨ m = truthStore ∨ m = inputStore ∨ m = proofStore ∨ m = answerStore ∨ m = rowStore from by
          simp only [TrimHonest.queryCursors, List.mem_cons, List.not_mem_nil, or_false] at h
          tauto)
    rw [fcother m hr ht ha, rd.cursor_eq, Function.update_of_ne ht, rc.other_cursor m hq]

end NearCubicGates.Adapters.Proximity.HonestRowTable
