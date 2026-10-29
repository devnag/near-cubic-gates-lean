import SourceAdapters.Proximity.HonestSource
import SourceAdapters.Proximity.RenderBlock
import SourceAdapters.Code.CountedBitLoading

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": physically pass the truth table and query answers
to the finite honest-assignment compiler, then load every raw result bit. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.HonestTableCall

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Code
open NearCubicGates.Adapters.Code.CellSending
open SourceRequests (State Script)
open SourceCallee (truthLengthReg)
open QueryStep (boundReg)
open TrimHonest (answerStore rowStore localBound)

def truthStore : Fin MM := 2
def tag : List Bool := [true, true]
def request {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (predicate : BitInput q → Bool) (answers : BitInput q) : ProofCall V :=
  .inr (.inr (honestTableInput predicate answers))

def rowWord {q : ℕ} (predicate : BitInput q → Bool) (answers : BitInput q) : List Bool :=
  List.ofFn (fun i : Fin (blockVariableBound q) => canonicalBlockAssignment predicate answers i.val)

def script : Script := .seq (RequestWriting.callLiteral t0 tag)
  (.seq (BitSending.script truthStore truthLengthReg) (.seq (BitSending.script answerStore boundReg)
    (.seq (.op .kcall) (CountedBitLoading.script rowStore localBound))))

theorem request_input {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (predicate : BitInput q → Bool) (answers : BitInput q) :
    proofCallInput V (request V predicate answers) =
      tag ++ List.ofFn (predicateTable predicate) ++ List.ofFn answers := by
  change tag ++ List.ofFn (Fin.addCases (predicateTable predicate) answers) = _
  have h : List.ofFn (Fin.addCases (predicateTable predicate) answers) =
      List.ofFn (predicateTable predicate) ++ List.ofFn answers :=
    List.ofFn_fin_append (predicateTable predicate) answers
  rw [h, List.append_assoc]

variable {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofSize : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofSize p.1))
    (budget : ProofCall V → ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofSize honest) budget)

theorem run (predicate : BitInput q → Bool) (answers : BitInput q)
    (Wd Lk Bk : ℕ) (input : List Bool) (a : State) (hc : Cst a)
    (htruth : a.ram truthStore = (List.ofFn (predicateTable predicate)).map Bool.toNat)
    (hanswers : a.ram answerStore = (List.ofFn answers).map Bool.toNat)
    (htruthLength : a.env truthLengthReg = 2 ^ q) (hanswerLength : a.env boundReg = q)
    (hrowLength : a.env localBound = blockVariableBound q)
    (hrow : a.ram rowStore = []) (hrowCursor : a.rc rowStore = 0) (hempty : a.kin = [])
    (htWidth : 2 ^ q < 2 ^ Wd) (haWidth : q < 2 ^ Wd) (hrWidth : blockVariableBound q < 2 ^ Wd)
    (hroom : 2 + 2 ^ q + q ≤ Lk) (hbudget : budget (request V predicate answers) ≤ Bk) :
    let C := SourceCallee.context V proofSize honest budget P Wd input Lk Bk
    Hs C script a
      (a.rc truthStore + a.rc answerStore + 8 * 2 ^ q + 8 * q + Lk + Bk + 7 * blockVariableBound q + 26)
      (fun b => b.ram rowStore = (rowWord predicate answers).map Bool.toNat ∧
        b.rc rowStore = blockVariableBound q ∧ b.kc = blockVariableBound q ∧
        b.rc truthStore = 2 ^ q ∧ b.rc answerStore = q ∧
        b.ip = a.ip ∧ b.out = a.out ∧ b.kin = [] ∧ b.kout = rowWord predicate answers ∧ Cst b ∧
        (∀ m, m ≠ rowStore → b.ram m = a.ram m) ∧
        (∀ m, m ≠ rowStore → m ≠ truthStore → m ≠ answerStore → b.rc m = a.rc m) ∧
        Fr a b [t0, c0, vJ]) := by
  dsimp only
  let C := SourceCallee.context V proofSize honest budget P Wd input Lk Bk
  have e0 := RequestWriting.call_literal C t0 tag a (by
    change a.kin.length + tag.length ≤ Lk
    simp only [hempty, List.length_nil, tag, List.length_cons]
    omega)
  let b := sent true (a.set t0 0) tag
  have cb : Cst b := by
    have h : Cst (a.set t0 0) := Cst.of_fr hc (Fr.set a 0 (T := [t0]) (by simp)) (by decide)
    exact ⟨h.z, h.one, h.two⟩
  obtain ⟨d, nd, ed, hd, dkin, _, cd, dip, dout, dram, dctruth, dcother, _, _, dfr⟩ :=
    BitSending.runs C truthStore truthLengthReg (by decide) (by decide) b cb
      (List.ofFn (predicateTable predicate)) htruth
      (by simpa only [b, sent_env, DS.set_env_ne _ _ (by decide : truthLengthReg ≠ t0), List.length_ofFn] using htruthLength)
      (by change (List.ofFn (predicateTable predicate)).length < 2 ^ Wd; simpa only [List.length_ofFn] using htWidth)
      (by change (a.kin ++ tag).length + (List.ofFn (predicateTable predicate)).length ≤ Lk
          simp only [hempty, List.nil_append, tag, List.length_cons, List.length_nil, List.length_ofFn]
          omega)
  have danswers : d.ram answerStore = (List.ofFn answers).map Bool.toNat := by rw [dram]; exact hanswers
  have dlength : d.env boundReg = (List.ofFn answers).length := by
    rw [dfr boundReg (by decide)]
    simpa only [b, sent_env, DS.set_env_ne _ _ (by decide : boundReg ≠ t0), List.length_ofFn] using hanswerLength
  obtain ⟨e, ne, ee, he, ekin, _, ce, eip, eout, eram, ecanswer, ecother, _, _, efr⟩ :=
    BitSending.runs C answerStore boundReg (by decide) (by decide) d cd (List.ofFn answers) danswers dlength
      (by change (List.ofFn answers).length < 2 ^ Wd; simpa only [List.length_ofFn] using haWidth)
      (by change d.kin.length + (List.ofFn answers).length ≤ Lk
          rw [dkin]
          change ((a.kin ++ tag) ++ List.ofFn (predicateTable predicate)).length + (List.ofFn answers).length ≤ Lk
          simp only [hempty, List.nil_append, List.length_append, tag, List.length_cons, List.length_nil, List.length_ofFn]
          omega)
  have erequest : e.kin = C.K.inw (request V predicate answers) := by
    rw [ekin, dkin]
    change ((a.kin ++ tag) ++ List.ofFn (predicateTable predicate)) ++ List.ofFn answers = _
    rw [hempty, List.nil_append]
    exact (request_input V predicate answers).symm
  have hout : C.K.outw (request V predicate answers) = rowWord predicate answers :=
    honestTableWord_input predicate answers
  have ecall := Ex.op (OpEx.kcall (C := C) (request V predicate answers) e erequest hbudget)
  rw [hout] at ecall
  let f := e.called (rowWord predicate answers)
  have cf : Cst f := ⟨ce.z, ce.one, ce.two⟩
  have flength : f.env localBound = (rowWord predicate answers).length := by
    change e.env localBound = _
    rw [efr localBound (by decide), dfr localBound (by decide)]
    simpa only [b, sent_env, DS.set_env_ne _ _ (by decide : localBound ≠ t0), rowWord, List.length_ofFn] using hrowLength
  have fempty : f.ram rowStore = [] := by change e.ram rowStore = []; rw [eram, dram]; exact hrow
  have fcursor : f.rc rowStore = 0 := by
    change e.rc rowStore = 0
    rw [ecother rowStore (by decide), dcother rowStore (by decide)]
    exact hrowCursor
  obtain ⟨g, ng, eg, hg, grow, _, gcrow, gkc, cg, gip, gout, gkin, gkout, gother, gfr⟩ :=
    CountedBitLoading.runs C rowStore localBound (by decide) (by decide) f cf
      (rowWord predicate answers) rfl rfl flength fempty fcursor
      (by change (rowWord predicate answers).length < 2 ^ Wd; simpa only [rowWord, List.length_ofFn] using hrWidth)
  refine ⟨g, _, Ex.seq e0 (Ex.seq ed (Ex.seq ee (Ex.seq ecall eg))), ?_, grow, ?_, ?_, ?_, ?_,
    gip.trans (eip.trans dip), gout.trans (eout.trans dout), gkin, gkout, cg, ?_, ?_, ?_⟩
  · change nd ≤ a.rc truthStore + 8 * (List.ofFn (predicateTable predicate)).length + 6 at hd
    rw [dcother answerStore (by decide)] at he
    change ne ≤ a.rc answerStore + 8 * (List.ofFn answers).length + 6 at he
    simp only [List.length_ofFn] at hd he
    change ng ≤ 7 * (rowWord predicate answers).length + 4 at hg
    simp only [rowWord, List.length_ofFn] at hg
    change (2 * tag.length + 1) + (nd + (ne + ((1 + Lk + Bk) + ng + 1) + 1) + 1) + 1 ≤ _
    simp only [tag, List.length_cons, List.length_nil]
    omega
  · simpa only [rowWord, List.length_ofFn] using gcrow
  · simpa only [rowWord, List.length_ofFn] using gkc
  · have h := (gother truthStore (by decide)).2
    change g.rc truthStore = e.rc truthStore at h
    rw [ecother truthStore (by decide), dctruth] at h
    simpa only [List.length_ofFn] using h
  · simpa only [List.length_ofFn] using (gother answerStore (by decide)).2.trans ecanswer
  · intro m hm
    rw [(gother m hm).1]
    change e.ram m = a.ram m
    rw [eram, dram]
    rfl
  · intro m hm ht ha
    rw [(gother m hm).2]
    change e.rc m = a.rc m
    rw [ecother m ha, dcother m ht]
    rfl
  · intro i hi
    have hi0 : i ≠ t0 := fun h => hi (by simp [h])
    have hi' : i ∉ [c0, vJ] := fun h => hi (List.mem_cons_of_mem t0 h)
    rw [gfr i hi']
    change e.env i = a.env i
    rw [efr i hi', dfr i hi']
    simp [b, sent, DS.set, hi0]

end NearCubicGates.Adapters.Proximity.HonestTableCall
