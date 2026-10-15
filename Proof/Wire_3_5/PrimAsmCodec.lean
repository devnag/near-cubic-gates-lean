import Proof.Wire_3_5.PrimAsmCopyNat
import Proof.Wire_3_5.Skeleton

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.Codec
open NearCubicWires NearCubicWires.WireExponent3_5
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-- The class mode's bit in the word: `THR` is `true`. -/
def modeBit : Mode → Bool
  | .thr => true
  | .sym => false

/-- The circuits' codes, in order. -/
def codeList (r : PrimRequest) : List ℕ := List.ofFn fun i => r.mode.code (r.circuits i)

/-- The carriers' codes, in order. -/
def carrierCodes (r : PrimRequest) : List ℕ := r.carriers.map Stars.Carrier.code

theorem flatten_ofFn_natWord {a : ℕ} (g : Fin a → ℕ) :
    (List.ofFn fun i => RepairRepresentation.natWord (g i)).flatten =
      (List.ofFn g).flatMap RepairRepresentation.natWord := by
  rw [List.flatMap, List.map_ofFn]
  rfl

/-- **The fields of a call's word.** -/
theorem word_eq (r : PrimRequest) :
    r.word = RepairRepresentation.natWord r.n ++ [modeBit r.mode] ++ RepairRepresentation.natWord r.a ++
      (codeList r).flatMap RepairRepresentation.natWord ++ RepairRepresentation.natListWord (carrierCodes r) ++
        RepairRepresentation.natListWord r.translation := by
  obtain ⟨n, mode, a, ha, circuits, carriers, translation⟩ := r
  cases mode <;> (unfold PrimRequest.word codeList carrierCodes; rw [flatten_ofFn_natWord]; rfl)

/-- **The framed word, field by field** (every field's marks, then the closing `false`). -/
theorem frame_word_eq (r : PrimRequest) :
    RepairOrdinary.frame r.word = marks (RepairRepresentation.natWord r.n) ++ [true, modeBit r.mode] ++
      marks (RepairRepresentation.natWord r.a) ++ marks ((codeList r).flatMap RepairRepresentation.natWord) ++
        marks (RepairRepresentation.natListWord (carrierCodes r)) ++
          marks (RepairRepresentation.natListWord r.translation) ++ [false] := by
  rw [word_eq]
  have hf : ∀ w : List Bool, RepairOrdinary.frame w = marks w ++ [false] := by
    intro w
    have := RepairOrdinary.Streaming.frame_append w []
    simpa [RepairOrdinary.frame] using this
  rw [hf]
  simp [WriteNat.marks_append, marks, List.append_assoc]

/-- The codes list has the call's arity as its length. -/
theorem codeList_length (r : PrimRequest) : (codeList r).length = r.a := by simp [codeList]

/-! ## The writer -/

section Writer
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat

variable {ns nr : ℕ} (cap : ℕ)

/-- The writer's register map for `n`: `R 0 = W 0`, scratch `W 3 … W 8`, `OP = W 9`. -/
def eN : Fin 8 ↪ Fin 12 := ⟨![0, 3, 4, 5, 6, 7, 8, 9], by decide⟩
/-- The writer's register map for `a`: `R 0 = W 1`. -/
def eA : Fin 8 ↪ Fin 12 := ⟨![1, 3, 4, 5, 6, 7, 8, 9], by decide⟩
/-- The copies' register map: `Q 0 = W 10` (count), scratch `W 3 … W 8`, `Q 7 = W 9 = OP`, `Q 8 = W 11`. -/
def eQ : Fin 9 ↪ Fin 12 := ⟨![10, 3, 4, 5, 6, 7, 8, 9, 11], by decide⟩

/-- **The PrimRequest writer**: append `frame req.word` to the end of `o`. `W 0 = n`, `W 1 = a`, `W 2` the mode flag
(`THR ↔ ≠ 0`); the codes' fields from `sc`, the carriers' list field from `sk`, the translation's list field from `st`
(each framed or raw); `W 9 = OP`; `W 3 … W 8`, `W 10`, `W 11` scratch. -/
def writeReqM (εc εk εt : Bool) (sc sk st o : Fin (ns + 1)) (W : Fin 12 ↪ Fin nr) : WM ns nr :=
  .seq (writeNatM o (eN.trans W)) (.seq (writeBitM o (W 9) (W 2)) (.seq (writeNatM o (eA.trans W))
    (.seq (FinalPass.Hash4.wcopyR (W 1) (W 10) (W 11)) (.seq (elemLoop εc sc o (eQ.trans W))
      (.seq (copyNatListM εk sk o (eQ.trans W)) (.seq (copyNatListM εt st o (eQ.trans W)) (emitC o (W 9) false)))))))

theorem Wne (W : Fin 12 ↪ Fin nr) {i j : Fin 12} (h : i ≠ j) : W i ≠ W j := W.injective.ne h

theorem emitC_appendO (o : Fin (ns + 1)) (OP : Fin nr) (b : Bool) (σ : WState ns nr) :
    ((σ.sets o ((σ.st o) ++ [b])).seth o (σ.sh o + 1)).setv OP (σ.val OP + 1) = appendO σ o OP [b] := rfl

theorem word_length (r : PrimRequest) : r.word.length = (RepairRepresentation.natWord r.n).length + 1 +
    (RepairRepresentation.natWord r.a).length + ((codeList r).flatMap RepairRepresentation.natWord).length +
      (RepairRepresentation.natListWord (carrierCodes r)).length + (RepairRepresentation.natListWord r.translation).length := by
  rw [word_eq]; simp; ring

/-- The writer's running time: the sum of its pieces' (polynomial in `n`, `a` and the fields' lengths). -/
def writeReqCost (r : PrimRequest) : ℕ :=
  (natBitLength r.n + 10) * (100 * r.n + 200) + 1 + (16 + 1 + ((natBitLength r.a + 10) * (100 * r.a + 200) + 1 +
    (18 * r.a + 3 + 1 + (64 * ((codeList r).flatMap RepairRepresentation.natWord).length + 64 * (codeList r).length + 1
      + 1 + (((carrierCodes r).length + 12) * (300 * (carrierCodes r).length + 300) +
        64 * (RepairRepresentation.natListWord (carrierCodes r)).length + 64 + 1 +
        ((r.translation.length + 12) * (300 * r.translation.length + 300) +
          64 * (RepairRepresentation.natListWord r.translation).length + 64 + 1 + 7))))))

/-- **The writer's spec**: `frame req.word` appended to `o`, each source past its field, the values `n, a` and the mode
flag kept, every scratch register `0` again, `OP` advanced by the word's length. -/
theorem writeReqM_spec (εc εk εt : Bool) (sc sk st o : Fin (ns + 1)) (hco : sc ≠ o) (hko : sk ≠ o) (hto : st ≠ o)
    (hck : sc ≠ sk) (hct : sc ≠ st) (hkt : sk ≠ st) (W : Fin 12 ↪ Fin nr) (r : PrimRequest)
    (pc rc pk rk pt rt : List Bool) (σ : WState ns nr)
    (hstc : σ.st sc = pc ++ enc εc ((codeList r).flatMap RepairRepresentation.natWord) ++ rc) (hshc : σ.sh sc = pc.length)
    (hstk : σ.st sk = pk ++ enc εk (RepairRepresentation.natListWord (carrierCodes r)) ++ rk) (hshk : σ.sh sk = pk.length)
    (hstt : σ.st st = pt ++ enc εt (RepairRepresentation.natListWord r.translation) ++ rt) (hsht : σ.sh st = pt.length)
    (ho : σ.sh o = (σ.st o).length) (hn : σ.val (W 0) = r.n) (ha : σ.val (W 1) = r.a)
    (hm : decide (σ.val (W 2) ≠ 0) = modeBit r.mode) (hz : ∀ i : Fin 12, 3 ≤ i.val → i ≠ 9 → σ.val (W i) = 0)
    (hcap : σ.val (W 9) + 3 * (RepairOrdinary.frame r.word).length + r.n + r.a + 8 * (carrierCodes r).length +
      8 * r.translation.length + 100 ≤ cap) :
    WExec cap (writeReqM εc εk εt sc sk st o W) σ
      ((((appendO σ o (W 9) (RepairOrdinary.frame r.word)).seth sc
        (pc.length + stp εc * ((codeList r).flatMap RepairRepresentation.natWord).length)).seth sk
          (pk.length + stp εk * (RepairRepresentation.natListWord (carrierCodes r)).length)).seth st
            (pt.length + stp εt * (RepairRepresentation.natListWord r.translation).length)) (writeReqCost r) := by
  -- lengths
  have hfl : (RepairOrdinary.frame r.word).length = 2 * r.word.length + 1 := by
    rw [RepairOrdinary.frame_length]
  have hwl := word_length r
  have hnl := natWord_length r.n
  have hal := natWord_length r.a
  have hnbn : natBitLength r.n ≤ (RepairRepresentation.natWord r.n).length := by omega
  have hnba : natBitLength r.a ≤ (RepairRepresentation.natWord r.a).length := by omega
  -- the register maps
  have eN0 : (eN.trans W) 0 = W 0 := rfl
  have eN7 : (eN.trans W) 7 = W 9 := rfl
  have eA0 : (eA.trans W) 0 = W 1 := rfl
  have eA7 : (eA.trans W) 7 = W 9 := rfl
  have eQ0 : (eQ.trans W) 0 = W 10 := rfl
  have eQ7 : (eQ.trans W) 7 = W 9 := rfl
  -- step 1: n
  have s1 := writeNatM_spec cap o (eN.trans W) σ (hz 3 (by decide) (by decide)) (hz 4 (by decide) (by decide))
    (hz 5 (by decide) (by decide)) (hz 6 (by decide) (by decide)) (hz 7 (by decide) (by decide))
    (hz 8 (by decide) (by decide)) ho (by rw [eN0, eN7, hn]; omega)
  rw [eN0, eN7, hn] at s1
  set σ1 := appendO σ o (W 9) (marks (RepairRepresentation.natWord r.n)) with hσ1
  have hv1 : ∀ i : Fin 12, i ≠ 9 → σ1.val (W i) = σ.val (W i) := by
    intro i hi; simp [σ1, Function.update_apply, Wne W hi]
  have ho1 : σ1.sh o = (σ1.st o).length := by simp [σ1, ho] <;> ring
  have hop1 : σ1.val (W 9) = σ.val (W 9) + 2 * (RepairRepresentation.natWord r.n).length := by
    simp only [σ1, appendO_val, Function.update_self, RepairOrdinary.Streaming.marks_length]
  -- step 2: the mode bit
  have s2 := writeBitM_spec cap o (W 9) (W 2) σ1 ho1 (by rw [hop1]; omega)
  rw [hv1 2 (by decide), hm] at s2
  set σ2 := appendO σ1 o (W 9) [true, modeBit r.mode] with hσ2
  have hv2 : ∀ i : Fin 12, i ≠ 9 → σ2.val (W i) = σ.val (W i) := by
    intro i hi; simp [σ2, Function.update_apply, Wne W hi, hv1 i hi]
  have ho2 : σ2.sh o = (σ2.st o).length := by simp [σ2, ho1] <;> ring
  have hop2 : σ2.val (W 9) = σ.val (W 9) + 2 * (RepairRepresentation.natWord r.n).length + 2 := by
    simp only [σ2, appendO_val, Function.update_self, hop1, List.length_cons, List.length_nil] <;> ring
  -- step 3: a
  have s3 := writeNatM_spec cap o (eA.trans W) σ2
    (by rw [show (eA.trans W) 1 = W 3 from rfl, hv2 3 (by decide)]; exact hz 3 (by decide) (by decide))
    (by rw [show (eA.trans W) 2 = W 4 from rfl, hv2 4 (by decide)]; exact hz 4 (by decide) (by decide))
    (by rw [show (eA.trans W) 3 = W 5 from rfl, hv2 5 (by decide)]; exact hz 5 (by decide) (by decide))
    (by rw [show (eA.trans W) 4 = W 6 from rfl, hv2 6 (by decide)]; exact hz 6 (by decide) (by decide))
    (by rw [show (eA.trans W) 5 = W 7 from rfl, hv2 7 (by decide)]; exact hz 7 (by decide) (by decide))
    (by rw [show (eA.trans W) 6 = W 8 from rfl, hv2 8 (by decide)]; exact hz 8 (by decide) (by decide))
    ho2 (by rw [eA0, eA7, hv2 1 (by decide), ha, hop2]; omega)
  rw [eA0, eA7, hv2 1 (by decide), ha] at s3
  set σ3 := appendO σ2 o (W 9) (marks (RepairRepresentation.natWord r.a)) with hσ3
  have hv3 : ∀ i : Fin 12, i ≠ 9 → σ3.val (W i) = σ.val (W i) := by
    intro i hi; simp [σ3, Function.update_apply, Wne W hi, hv2 i hi]
  have ho3 : σ3.sh o = (σ3.st o).length := by simp [σ3, ho2] <;> ring
  have hop3 : σ3.val (W 9) = σ.val (W 9) + 2 * (RepairRepresentation.natWord r.n).length + 2 +
      2 * (RepairRepresentation.natWord r.a).length := by
    simp only [σ3, appendO_val, Function.update_self, hop2, RepairOrdinary.Streaming.marks_length]
  -- step 4: the count
  have s4 := FinalPass.Hash4.wcopyR_spec cap (W 1) (W 10) (W 11) (Wne W (by decide)) (Wne W (by decide))
    (Wne W (by decide)) σ3 (by rw [hv3 10 (by decide)]; exact hz 10 (by decide) (by decide))
    (by rw [hv3 11 (by decide)]; exact hz 11 (by decide) (by decide)) (by rw [hv3 1 (by decide), ha]; omega)
  rw [hv3 1 (by decide), ha] at s4
  set σ4 := σ3.setv (W 10) r.a with hσ4
  -- step 5: the codes
  have s5 := elemLoop_spec cap εc sc o hco (eQ.trans W) (codeList r) pc rc σ4
    (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hco, hstc])
    (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hco, hshc])
    (by simp [σ4, ho3])
    (by rw [eQ0, codeList_length]; simp [σ4])
    (by rw [show (eQ.trans W) 1 = W 3 from rfl]; simp [σ4, Function.update_apply, Wne W (show (3 : Fin 12) ≠ 10 by decide),
      hv3 3 (by decide), hz 3 (by decide) (by decide)])
    (by rw [show (eQ.trans W) 2 = W 4 from rfl]; simp [σ4, Function.update_apply, Wne W (show (4 : Fin 12) ≠ 10 by decide),
      hv3 4 (by decide), hz 4 (by decide) (by decide)])
    (by rw [eQ0]; simp [σ4]; omega)
    (by rw [eQ7]; simp only [σ4, WState.setv_val, Function.update_apply, if_neg (Wne W (show (9 : Fin 12) ≠ 10 by decide)),
      hop3]; omega)
  rw [eQ7, eQ0] at s5
  set σ5 := ((appendO σ4 o (W 9) (marks ((codeList r).flatMap RepairRepresentation.natWord))).seth sc
    (pc.length + stp εc * ((codeList r).flatMap RepairRepresentation.natWord).length)).setv (W 10) 0 with hσ5
  have hv5 : ∀ i : Fin 12, i ≠ 9 → i ≠ 10 → σ5.val (W i) = σ.val (W i) := by
    intro i hi h10; simp [σ5, σ4, Function.update_apply, Wne W hi, Wne W h10, hv3 i hi]
  have hv510 : σ5.val (W 10) = 0 := by simp [σ5]
  have ho5 : σ5.sh o = (σ5.st o).length := by simp [σ5, σ4, Function.update_apply, Ne.symm hco, ho3] <;> ring
  have hop5 : σ5.val (W 9) = σ3.val (W 9) + 2 * ((codeList r).flatMap RepairRepresentation.natWord).length := by
    simp only [σ5, WState.setv_val, Function.update_apply, if_neg (Wne W (show (9 : Fin 12) ≠ 10 by decide)),
      WState.seth_val, appendO_val, Function.update_self, σ4, RepairOrdinary.Streaming.marks_length]
    simp
  -- step 6: the carriers
  have hQ5 : ∀ i : Fin 9, i ≠ 7 → σ5.val ((eQ.trans W) i) = 0 := by
    intro i hi
    fin_cases i
    · exact hv510
    all_goals first
      | exact absurd rfl hi
      | (simp only [Function.Embedding.trans_apply]
         rw [hv5 _ (by decide) (by decide)]; exact hz _ (by decide) (by decide))
  have s6 := copyNatListM_spec cap εk sk o hko (eQ.trans W) (carrierCodes r) pk rk σ5
    (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hko, Ne.symm hck, hstk])
    (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hko, Ne.symm hck, hshk]) ho5 hQ5
    (by rw [eQ7, hop5, hop3]; omega)
  rw [eQ7] at s6
  set σ6 := (appendO σ5 o (W 9) (marks (RepairRepresentation.natListWord (carrierCodes r)))).seth sk
    (pk.length + stp εk * (RepairRepresentation.natListWord (carrierCodes r)).length) with hσ6
  have hv6 : ∀ i : Fin 12, i ≠ 9 → σ6.val (W i) = σ5.val (W i) := by
    intro i hi; simp [σ6, Function.update_apply, Wne W hi]
  have ho6 : σ6.sh o = (σ6.st o).length := by simp [σ6, Function.update_apply, Ne.symm hko, ho5] <;> ring
  have hop6 : σ6.val (W 9) = σ5.val (W 9) + 2 * (RepairRepresentation.natListWord (carrierCodes r)).length := by
    simp only [σ6, WState.seth_val, appendO_val, Function.update_self, RepairOrdinary.Streaming.marks_length]
  -- step 7: the translation
  have hQ6 : ∀ i : Fin 9, i ≠ 7 → σ6.val ((eQ.trans W) i) = 0 := by
    intro i hi
    rw [show σ6.val ((eQ.trans W) i) = σ5.val ((eQ.trans W) i) by
      simp only [Function.Embedding.trans_apply]
      fin_cases i <;> first | exact absurd rfl hi | exact hv6 _ (by decide)]
    exact hQ5 i hi
  have s7 := copyNatListM_spec cap εt st o hto (eQ.trans W) r.translation pt rt σ6
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hto, Ne.symm hkt, Ne.symm hct, hstt])
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hto, Ne.symm hkt, Ne.symm hct, hsht]) ho6 hQ6
    (by rw [eQ7, hop6, hop5, hop3]; omega)
  rw [eQ7] at s7
  set σ7 := (appendO σ6 o (W 9) (marks (RepairRepresentation.natListWord r.translation))).seth st
    (pt.length + stp εt * (RepairRepresentation.natListWord r.translation).length) with hσ7
  have ho7 : σ7.sh o = (σ7.st o).length := by simp [σ7, Function.update_apply, Ne.symm hto, ho6] <;> ring
  have hop7 : σ7.val (W 9) = σ6.val (W 9) + 2 * (RepairRepresentation.natListWord r.translation).length := by
    simp only [σ7, WState.seth_val, appendO_val, Function.update_self, RepairOrdinary.Streaming.marks_length]
  -- step 8: the closing `false`
  have s8 := emitC_spec cap o (W 9) false σ7 ho7 (by rw [hop7, hop6, hop5, hop3]; omega)
  rw [emitC_appendO] at s8
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    (WExec.seq s7 s8))))))) ?_ (le_of_eq (by unfold writeReqCost; ring))
  -- the final state
  have hfw := frame_word_eq r
  have hz10 : σ.val (W 10) = 0 := hz 10 (by decide) (by decide)
  apply WState.eq
  · funext j
    by_cases hjo : j = o
    · subst hjo
      simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hco.symm, hko.symm, hto.symm, hfw]
      ring
    · by_cases hjt : j = st
      · subst hjt; simp [σ7, Function.update_apply, hjo]
      · by_cases hjk : j = sk
        · subst hjk; simp [σ7, σ6, Function.update_apply, hjo, hjt]
        · by_cases hjc : j = sc
          · subst hjc; simp [σ7, σ6, σ5, σ4, Function.update_apply, hjo, hjt, hjk]
          · simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hjo, hjt, hjk, hjc]
  · funext j
    by_cases hjo : j = o
    · subst hjo
      simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hco.symm, hko.symm, hto.symm, hfw, marks]
    · simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hjo]
  · funext j
    by_cases hj9 : j = W 9
    · subst hj9
      simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, Wne W (show (9 : Fin 12) ≠ 10 by decide), hfw]
      ring
    · by_cases hj10 : j = W 10
      · subst hj10; simp [σ7, σ6, σ5, σ4, Function.update_apply, hj9, hz10]
      · simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hj9, hj10]
  · simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1]

end Writer

/-! ## The parser -/

section Parser
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat

variable {ns nr : ℕ} (cap : ℕ)

/-- Read one logical bit into the flag `fl` (`fl += bit`). -/
def readBitM (ε : Bool) (i : Fin (ns + 1)) (fl : Fin nr) : WM ns nr :=
  .seq (preE ε i) (.seq (.ifs i (.inc fl) .skip) (.fwd i))

theorem readBitM_spec (ε : Bool) (i : Fin (ns + 1)) (fl : Fin nr) (σ : WState ns nr) (hc : σ.val fl < cap) :
    WExec cap (readBitM ε i fl) σ
      ((σ.setv fl (σ.val fl + (readTapeBit (σ.st i) (σ.sh i + off ε)).toNat)).seth i (σ.sh i + stp ε)) 8 := by
  have hs := stp_eq ε
  have ho := off_le ε
  have h1 := preE_spec cap ε i σ
  set σ1 := σ.seth i (σ.sh i + off ε) with hσ1
  set b := readTapeBit (σ.st i) (σ.sh i + off ε) with hb
  have hbit : wbit σ1 i = b := by simp [σ1, wbit, b]
  have h2 : WExec cap (.ifs i (.inc fl) .skip) σ1 (σ1.setv fl (σ1.val fl + b.toNat)) 4 := by
    cases hbv : b with
    | true => exact WExec.ifsT (by rw [hbit, hbv]) (WExec.inc fl σ1 (by simpa [σ1] using hc))
    | false =>
      have e : σ1.setv fl (σ1.val fl + false.toNat) = σ1 := by simp [wsetv_same]
      rw [e]; exact WExec.mono (WExec.ifsF (by rw [hbit, hbv]) (WExec.skip σ1)) (by omega)
  have h3 := WExec.fwd (cap := cap) i (σ1.setv fl (σ1.val fl + b.toNat))
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by omega)
  apply WState.eq
  · funext j; by_cases hj : j = i
    · subst hj; simp [σ1]; omega
    · simp [σ1, Function.update_apply, hj]
  · simp [σ1]
  · simp [σ1]
  · simp [σ1]

/-- The parser's register maps: `n` read with scratch `W 3, W 4, W 5, W 8`; the copies with `Q 0 = W 10`, scratch
`W 3 … W 8`, `Q 8 = W 11`, and their own position counter `Q 7`: `W 9` (codes), `W 12` (carriers), `W 13`
(translation). -/
def pQc : Fin 9 ↪ Fin 14 := ⟨![10, 3, 4, 5, 6, 7, 8, 9, 11], by decide⟩
def pQk : Fin 9 ↪ Fin 14 := ⟨![10, 3, 4, 5, 6, 7, 8, 12, 11], by decide⟩
def pQt : Fin 9 ↪ Fin 14 := ⟨![10, 3, 4, 5, 6, 7, 8, 13, 11], by decide⟩

/-- **The PrimRequest parser**: from `enc true req.word` on stream `s` (the framed input), `W 0 := n`, `W 2 += mode bit`,
`W 1 := a`; the codes' fields appended to `dc`, the carriers' list field to `dk`, the translation's list field to `dt`
(framed, counted in `W 9`, `W 12`, `W 13`). -/
def parseReqM (s dc dk dt : Fin (ns + 1)) (W : Fin 14 ↪ Fin nr) : WM ns nr :=
  .seq (readNatM true s (W 3) (W 4) (W 0) (W 5) (W 8)) (.seq (readBitM true s (W 2))
    (.seq (readNatM true s (W 3) (W 4) (W 1) (W 5) (W 8)) (.seq (FinalPass.Hash4.wcopyR (W 1) (W 10) (W 11))
      (.seq (elemLoop true s dc (pQc.trans W)) (.seq (copyNatListM true s dk (pQk.trans W))
        (copyNatListM true s dt (pQt.trans W)))))))

@[simp] theorem pQc_apply (i : Fin 9) : pQc i = ![10, 3, 4, 5, 6, 7, 8, 9, 11] i := rfl
@[simp] theorem pQk_apply (i : Fin 9) : pQk i = ![10, 3, 4, 5, 6, 7, 8, 12, 11] i := rfl
@[simp] theorem pQt_apply (i : Fin 9) : pQt i = ![10, 3, 4, 5, 6, 7, 8, 13, 11] i := rfl
@[simp] theorem stp_true : stp true = 2 := rfl

theorem Wne14 (W : Fin 14 ↪ Fin nr) {i j : Fin 14} (h : i ≠ j) : W i ≠ W j := W.injective.ne h

theorem marks_word_eq (r : PrimRequest) :
    marks r.word = marks (RepairRepresentation.natWord r.n) ++ marks [modeBit r.mode] ++
      marks (RepairRepresentation.natWord r.a) ++ marks ((codeList r).flatMap RepairRepresentation.natWord) ++
        marks (RepairRepresentation.natListWord (carrierCodes r)) ++
          marks (RepairRepresentation.natListWord r.translation) := by
  rw [word_eq]; simp only [marks_append]

/-- The parser's running time. -/
def parseReqCost (r : PrimRequest) : ℕ :=
  (natBitLength r.n + 2) * (40 * 2 ^ natBitLength r.n + 40) + 1 + (8 + 1 +
    ((natBitLength r.a + 2) * (40 * 2 ^ natBitLength r.a + 40) + 1 + (18 * r.a + 3 + 1 +
      (64 * ((codeList r).flatMap RepairRepresentation.natWord).length + 64 * (codeList r).length + 1 + 1 +
        (((carrierCodes r).length + 12) * (300 * (carrierCodes r).length + 300) +
          64 * (RepairRepresentation.natListWord (carrierCodes r)).length + 64 + 1 +
          ((r.translation.length + 12) * (300 * r.translation.length + 300) +
            64 * (RepairRepresentation.natListWord r.translation).length + 64))))))

/-- **The parser's spec**: from `marks req.word` on `s`, the three values `n`, `a`, the mode bit into `W 0`, `W 1`, `W 2`,
the codes', carriers' and translation's fields appended to `dc`, `dk`, `dt` (counted), `s` past the word, every
scratch register `0` again. -/
theorem parseReqM_spec (s dc dk dt : Fin (ns + 1)) (hsc : s ≠ dc) (hsk : s ≠ dk) (hst' : s ≠ dt) (hck : dc ≠ dk)
    (hct : dc ≠ dt) (hkt : dk ≠ dt) (W : Fin 14 ↪ Fin nr) (r : PrimRequest) (pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st s = pre ++ marks r.word ++ rest) (hsh : σ.sh s = pre.length)
    (hoc : σ.sh dc = (σ.st dc).length) (hok : σ.sh dk = (σ.st dk).length) (hot : σ.sh dt = (σ.st dt).length)
    (hz : ∀ i : Fin 14, i ≠ 9 → i ≠ 12 → i ≠ 13 → σ.val (W i) = 0)
    (hcap : σ.val (W 9) + σ.val (W 12) + σ.val (W 13) + 3 * (RepairOrdinary.frame r.word).length + 8 * r.n +
      8 * r.a + 8 * (carrierCodes r).length + 8 * r.translation.length + 100 ≤ cap) :
    WExec cap (parseReqM s dc dk dt W) σ
      (((((appendO (appendO (appendO σ dc (W 9) (marks ((codeList r).flatMap RepairRepresentation.natWord)))
        dk (W 12) (marks (RepairRepresentation.natListWord (carrierCodes r)))) dt (W 13)
          (marks (RepairRepresentation.natListWord r.translation))).seth s (pre.length + 2 * r.word.length)).setv
            (W 0) r.n).setv (W 1) r.a).setv (W 2) (modeBit r.mode).toNat)
      (parseReqCost r) := by
  have hfl : (RepairOrdinary.frame r.word).length = 2 * r.word.length + 1 := by rw [RepairOrdinary.frame_length]
  have hwl := word_length r
  have hPn := two_pow_natBitLength_le r.n
  have hPa := two_pow_natBitLength_le r.a
  have hmw := marks_word_eq r
  have hs2 : stp true = 2 := rfl
  -- step 1: n
  have p1 := readNatM_spec cap true s (W 3) (W 4) (W 0) (W 5) (W 8) (Wne14 W (by decide)) (Wne14 W (by decide))
    (Wne14 W (by decide)) (Wne14 W (by decide)) (Wne14 W (by decide)) (Wne14 W (by decide)) (Wne14 W (by decide))
    (Wne14 W (by decide)) (Wne14 W (by decide)) (Wne14 W (by decide)) r.n pre
    (marks [modeBit r.mode] ++ marks (RepairRepresentation.natWord r.a) ++
      marks ((codeList r).flatMap RepairRepresentation.natWord) ++
        marks (RepairRepresentation.natListWord (carrierCodes r)) ++
          marks (RepairRepresentation.natListWord r.translation) ++ rest) σ
    (by rw [hst, hmw]; simp [ParseNat.enc, List.append_assoc]) hsh
    (hz 3 (by decide) (by decide) (by decide)) (hz 4 (by decide) (by decide) (by decide))
    (hz 5 (by decide) (by decide) (by decide)) (hz 8 (by decide) (by decide) (by decide))
    (by rw [hz 0 (by decide) (by decide) (by decide), pow_succ]; omega)
  rw [hz 0 (by decide) (by decide) (by decide), Nat.zero_add, hs2] at p1
  set σ1 := (σ.seth s (pre.length + 2 * (RepairRepresentation.natWord r.n).length)).setv (W 0) r.n with hσ1
  -- step 2: the mode bit
  have p2 := readBitM_spec cap true s (W 2) σ1 (by simp [σ1, Function.update_apply,
    Wne14 W (show (2 : Fin 14) ≠ 0 by decide), hz 2 (by decide) (by decide) (by decide)]; omega)
  have hbit : readTapeBit (σ1.st s) (σ1.sh s + off true) = modeBit r.mode := by
    have e1 : σ1.st s = (pre ++ marks (RepairRepresentation.natWord r.n)) ++ (enc true [modeBit r.mode] ++
        (marks (RepairRepresentation.natWord r.a) ++ marks ((codeList r).flatMap RepairRepresentation.natWord) ++
          marks (RepairRepresentation.natListWord (carrierCodes r)) ++
            marks (RepairRepresentation.natListWord r.translation) ++ rest)) := by
      simp [σ1, hst, hmw, ParseNat.enc, List.append_assoc]
    have e2 : σ1.sh s + off true = (pre ++ marks (RepairRepresentation.natWord r.n)).length + (stp true * 0 + off true) := by
      simp [σ1, RepairOrdinary.Streaming.marks_length]
    rw [e1, e2, read_pre, read_enc_bit true _ _ 0 (by simp)]
    simp
  rw [hbit, hs2] at p2
  set σ2 := (σ1.setv (W 2) (σ1.val (W 2) + (modeBit r.mode).toNat)).seth s (σ1.sh s + 2) with hσ2
  have hσ2v2 : σ2.val (W 2) = (modeBit r.mode).toNat := by
    simp [σ2, σ1, Function.update_apply, Wne14 W (show (2 : Fin 14) ≠ 0 by decide),
      hz 2 (by decide) (by decide) (by decide)]
  have hv2 : ∀ i : Fin 14, i ≠ 0 → i ≠ 2 → σ2.val (W i) = σ.val (W i) := by
    intro i h0 h2; simp [σ2, σ1, Function.update_apply, Wne14 W h0, Wne14 W h2]
  have hσ2sh : σ2.sh s = pre.length + 2 * (RepairRepresentation.natWord r.n).length + 2 := by simp [σ2, σ1]
  -- step 3: a
  have p3 := readNatM_spec cap true s (W 3) (W 4) (W 1) (W 5) (W 8) (Wne14 W (by decide)) (Wne14 W (by decide))
    (Wne14 W (by decide)) (Wne14 W (by decide)) (Wne14 W (by decide)) (Wne14 W (by decide)) (Wne14 W (by decide))
    (Wne14 W (by decide)) (Wne14 W (by decide)) (Wne14 W (by decide)) r.a
    (pre ++ marks (RepairRepresentation.natWord r.n) ++ marks [modeBit r.mode])
    (marks ((codeList r).flatMap RepairRepresentation.natWord) ++
      marks (RepairRepresentation.natListWord (carrierCodes r)) ++
        marks (RepairRepresentation.natListWord r.translation) ++ rest) σ2
    (by simp [σ2, σ1, hst, hmw, ParseNat.enc, List.append_assoc])
    (by rw [hσ2sh]; simp [RepairOrdinary.Streaming.marks_length]; ring)
    (by rw [hv2 3 (by decide) (by decide)]; exact hz 3 (by decide) (by decide) (by decide))
    (by rw [hv2 4 (by decide) (by decide)]; exact hz 4 (by decide) (by decide) (by decide))
    (by rw [hv2 5 (by decide) (by decide)]; exact hz 5 (by decide) (by decide) (by decide))
    (by rw [hv2 8 (by decide) (by decide)]; exact hz 8 (by decide) (by decide) (by decide))
    (by rw [hv2 1 (by decide) (by decide), hz 1 (by decide) (by decide) (by decide), pow_succ]; omega)
  rw [hv2 1 (by decide) (by decide), hz 1 (by decide) (by decide) (by decide), Nat.zero_add, hs2] at p3
  set σ3 := (σ2.seth s ((pre ++ marks (RepairRepresentation.natWord r.n) ++ marks [modeBit r.mode]).length +
    2 * (RepairRepresentation.natWord r.a).length)).setv (W 1) r.a with hσ3
  have hv3 : ∀ i : Fin 14, i ≠ 0 → i ≠ 1 → i ≠ 2 → σ3.val (W i) = σ.val (W i) := by
    intro i h0 h1 h2; simp [σ3, Function.update_apply, Wne14 W h1, hv2 i h0 h2]
  -- step 4: the count
  have p4 := FinalPass.Hash4.wcopyR_spec cap (W 1) (W 10) (W 11) (Wne14 W (by decide)) (Wne14 W (by decide))
    (Wne14 W (by decide)) σ3
    (by rw [hv3 10 (by decide) (by decide) (by decide)]; exact hz 10 (by decide) (by decide) (by decide))
    (by rw [hv3 11 (by decide) (by decide) (by decide)]; exact hz 11 (by decide) (by decide) (by decide))
    (by simp [σ3]; omega)
  have hσ3a : σ3.val (W 1) = r.a := by simp [σ3]
  rw [hσ3a] at p4
  set σ4 := σ3.setv (W 10) r.a with hσ4
  have hσ4sh : σ4.sh s = (pre ++ marks (RepairRepresentation.natWord r.n) ++ marks [modeBit r.mode] ++
      marks (RepairRepresentation.natWord r.a)).length := by
    simp [σ4, σ3, RepairOrdinary.Streaming.marks_length]; ring
  -- step 5: the codes
  have p5 := elemLoop_spec cap true s dc hsc (pQc.trans W) (codeList r)
    (pre ++ marks (RepairRepresentation.natWord r.n) ++ marks [modeBit r.mode] ++
      marks (RepairRepresentation.natWord r.a))
    (marks (RepairRepresentation.natListWord (carrierCodes r)) ++
      marks (RepairRepresentation.natListWord r.translation) ++ rest) σ4
    (by simp [σ4, σ3, σ2, σ1, hst, hmw, ParseNat.enc, List.append_assoc]) hσ4sh
    (by simp [σ4, σ3, σ2, σ1, Function.update_apply, Ne.symm hsc, hoc])
    (by show σ4.val (W 10) = (codeList r).length; simp [σ4, codeList_length])
    (by show σ4.val (W 3) = 0; simp [σ4, Function.update_apply, Wne14 W (show (3 : Fin 14) ≠ 10 by decide),
      hv3 3 (by decide) (by decide) (by decide), hz 3 (by decide) (by decide) (by decide)])
    (by show σ4.val (W 4) = 0; simp [σ4, Function.update_apply, Wne14 W (show (4 : Fin 14) ≠ 10 by decide),
      hv3 4 (by decide) (by decide) (by decide), hz 4 (by decide) (by decide) (by decide)])
    (by show σ4.val (W 10) ≤ cap; simp [σ4]; omega)
    (by show σ4.val (W 9) + 2 * ((codeList r).flatMap RepairRepresentation.natWord).length + 2 ≤ cap
        simp only [σ4, WState.setv_val, Function.update_apply, if_neg (Wne14 W (show (9 : Fin 14) ≠ 10 by decide))]
        rw [hv3 9 (by decide) (by decide) (by decide)]; omega)
  set σ5 := ((appendO σ4 dc ((pQc.trans W) 7) (marks ((codeList r).flatMap RepairRepresentation.natWord))).seth s
    ((pre ++ marks (RepairRepresentation.natWord r.n) ++ marks [modeBit r.mode] ++
      marks (RepairRepresentation.natWord r.a)).length + stp true *
        ((codeList r).flatMap RepairRepresentation.natWord).length)).setv ((pQc.trans W) 0) 0 with hσ5
  have hpc7 : (pQc.trans W) 7 = W 9 := rfl
  have hpc0 : (pQc.trans W) 0 = W 10 := rfl
  have hv5 : ∀ i : Fin 14, i ≠ 0 → i ≠ 1 → i ≠ 2 → i ≠ 9 → σ5.val (W i) = σ.val (W i) := by
    intro i h0 h1 h2 h9
    simp only [σ5, hpc7, hpc0, WState.setv_val, WState.seth_val, appendO_val, σ4, Function.update_apply]
    by_cases h10 : i = 10
    · subst h10; simp [hz 10 (by decide) (by decide) (by decide)]
    · rw [if_neg (Wne14 W h10), if_neg (Wne14 W h9), if_neg (Wne14 W h10), hv3 i h0 h1 h2]
  -- step 6: the carriers
  have hQk : ∀ i : Fin 9, i ≠ 7 → σ5.val ((pQk.trans W) i) = 0 := by
    intro i hi
    fin_cases i
    all_goals first
      | exact absurd rfl hi
      | (simp only [Function.Embedding.trans_apply]
         rw [hv5 _ (by decide) (by decide) (by decide) (by decide)]
         exact hz _ (by decide) (by decide) (by decide))
  have p6 := copyNatListM_spec cap true s dk hsk (pQk.trans W) (carrierCodes r)
    (pre ++ marks (RepairRepresentation.natWord r.n) ++ marks [modeBit r.mode] ++
      marks (RepairRepresentation.natWord r.a) ++ marks ((codeList r).flatMap RepairRepresentation.natWord))
    (marks (RepairRepresentation.natListWord r.translation) ++ rest) σ5
    (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hsc, hst, hmw, ParseNat.enc, List.append_assoc])
    (by simp [σ5, σ4, RepairOrdinary.Streaming.marks_length, List.length_append]; ring)
    (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, Ne.symm hsk, hck.symm, hok])
    hQk
    (by show σ5.val (W 12) + 8 * (carrierCodes r).length +
          2 * (RepairRepresentation.natListWord (carrierCodes r)).length + 16 ≤ cap
        rw [hv5 12 (by decide) (by decide) (by decide) (by decide)]; omega)
  have hpk7 : (pQk.trans W) 7 = W 12 := rfl
  rw [hpk7] at p6
  set σ6 := (appendO σ5 dk (W 12) (marks (RepairRepresentation.natListWord (carrierCodes r)))).seth s
    ((pre ++ marks (RepairRepresentation.natWord r.n) ++ marks [modeBit r.mode] ++
      marks (RepairRepresentation.natWord r.a) ++ marks ((codeList r).flatMap RepairRepresentation.natWord)).length +
        stp true * (RepairRepresentation.natListWord (carrierCodes r)).length) with hσ6
  have hv6 : ∀ i : Fin 14, i ≠ 0 → i ≠ 1 → i ≠ 2 → i ≠ 9 → i ≠ 12 → σ6.val (W i) = σ.val (W i) := by
    intro i h0 h1 h2 h9 h12
    simp only [σ6, WState.seth_val, appendO_val, Function.update_apply, if_neg (Wne14 W h12)]
    exact hv5 i h0 h1 h2 h9
  -- step 7: the translation
  have hQt : ∀ i : Fin 9, i ≠ 7 → σ6.val ((pQt.trans W) i) = 0 := by
    intro i hi
    fin_cases i
    all_goals first
      | exact absurd rfl hi
      | (simp only [Function.Embedding.trans_apply]
         rw [hv6 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
         exact hz _ (by decide) (by decide) (by decide))
  have p7 := copyNatListM_spec cap true s dt hst' (pQt.trans W) r.translation
    (pre ++ marks (RepairRepresentation.natWord r.n) ++ marks [modeBit r.mode] ++
      marks (RepairRepresentation.natWord r.a) ++ marks ((codeList r).flatMap RepairRepresentation.natWord) ++
        marks (RepairRepresentation.natListWord (carrierCodes r))) rest σ6
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hsc, hsk, hst, hmw, ParseNat.enc, List.append_assoc])
    (by simp [σ6, RepairOrdinary.Streaming.marks_length, List.length_append]; ring)
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, Ne.symm hst', hct.symm, hkt.symm, hot])
    hQt
    (by show σ6.val (W 13) + 8 * r.translation.length +
          2 * (RepairRepresentation.natListWord r.translation).length + 16 ≤ cap
        rw [hv6 13 (by decide) (by decide) (by decide) (by decide) (by decide)]; omega)
  have hpt7 : (pQt.trans W) 7 = W 13 := rfl
  rw [hpt7] at p7
  refine WExec.cast cap (WExec.seq p1 (WExec.seq p2 (WExec.seq p3 (WExec.seq p4 (WExec.seq p5 (WExec.seq p6 p7))))))
    ?_ (le_of_eq (by unfold parseReqCost; rw [codeList_length]))
  -- the final state
  apply WState.eq
  · funext j
    by_cases hjs : j = s
    · subst hjs
      simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hsc, hsk, hst', RepairOrdinary.Streaming.marks_length, hwl]
      ring
    · by_cases hjc : j = dc
      · subst hjc; simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hjs, hck, hct]
      · by_cases hjk : j = dk
        · subst hjk; simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hjs, hjc, hkt]
        · by_cases hjt : j = dt
          · subst hjt; simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hjs, hjc, hjk]
          · simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hjs, hjc, hjk, hjt]
  · funext j
    by_cases hjc : j = dc
    · subst hjc; simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hck, hct, Ne.symm hsc]
    · by_cases hjk : j = dk
      · subst hjk; simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hjc, hkt, Ne.symm hsk]
      · by_cases hjt : j = dt
        · subst hjt; simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hjc, hjk, Ne.symm hst']
        · simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hjc, hjk, hjt]
  · funext j
    by_cases h2 : j = W 2
    · subst h2; simp [Function.update_apply, Wne14 W (show (2 : Fin 14) ≠ 1 by decide),
        Wne14 W (show (2 : Fin 14) ≠ 0 by decide)]
      simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, Wne14 W (show (2 : Fin 14) ≠ 13 by decide),
        Wne14 W (show (2 : Fin 14) ≠ 12 by decide), Wne14 W (show (2 : Fin 14) ≠ 10 by decide),
        Wne14 W (show (2 : Fin 14) ≠ 9 by decide), Wne14 W (show (2 : Fin 14) ≠ 1 by decide),
        Wne14 W (show (2 : Fin 14) ≠ 0 by decide), hz 2 (by decide) (by decide) (by decide)]
    · by_cases h1 : j = W 1
      · subst h1; simp [σ6, σ5, σ4, σ3, Function.update_apply, h2, Wne14 W (show (1 : Fin 14) ≠ 13 by decide),
          Wne14 W (show (1 : Fin 14) ≠ 12 by decide), Wne14 W (show (1 : Fin 14) ≠ 10 by decide),
          Wne14 W (show (1 : Fin 14) ≠ 9 by decide)]
      · by_cases h0 : j = W 0
        · subst h0; simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, h2, h1,
            Wne14 W (show (0 : Fin 14) ≠ 13 by decide), Wne14 W (show (0 : Fin 14) ≠ 12 by decide),
            Wne14 W (show (0 : Fin 14) ≠ 10 by decide), Wne14 W (show (0 : Fin 14) ≠ 9 by decide)]
        · by_cases h10 : j = W 10
          · subst h10; simp [σ6, σ5, hpc0, Function.update_apply, h2, h1, h0,
              Wne14 W (show (10 : Fin 14) ≠ 13 by decide), Wne14 W (show (10 : Fin 14) ≠ 12 by decide),
              hz 10 (by decide) (by decide) (by decide)]
          · by_cases h9 : j = W 9
            · subst h9; simp [σ6, σ5, σ4, σ3, σ2, σ1, hpc7, hpc0, Function.update_apply, h2, h1, h0, h10,
                Wne14 W (show (9 : Fin 14) ≠ 13 by decide), Wne14 W (show (9 : Fin 14) ≠ 12 by decide)]
            · by_cases h12 : j = W 12
              · subst h12; simp [σ6, σ5, σ4, σ3, σ2, σ1, hpc7, hpc0, Function.update_apply, h2, h1, h0, h10, h9,
                  Wne14 W (show (12 : Fin 14) ≠ 13 by decide)]
              · by_cases h13 : j = W 13
                · subst h13; simp [σ6, σ5, σ4, σ3, σ2, σ1, hpc7, hpc0, Function.update_apply, h2, h1, h0, h10, h9,
                    h12]
                · simp [σ6, σ5, σ4, σ3, σ2, σ1, hpc7, hpc0, Function.update_apply, h2, h1, h0, h10, h9, h12, h13]
  · simp [σ6, σ5, σ4, σ3, σ2, σ1]

end Parser

/-! ## The round trip -/

section RoundTrip
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat

variable {ns nr : ℕ} (cap : ℕ)

/-- The writer's registers inside the parser's: `W 0 … W 11`. -/
def eR : Fin 12 ↪ Fin 14 := Fin.castLEEmb (by norm_num)

@[simp] theorem eR_apply (i : Fin 12) : eR i = Fin.castLE (by norm_num) i := rfl

/-- **Parse, rewind the three field streams, write**. -/
def roundTripM (s dc dk dt o : Fin (ns + 1)) (W : Fin 14 ↪ Fin nr) : WM ns nr :=
  .seq (parseReqM s dc dk dt W) (.seq (WM.rewind dc (W 9)) (.seq (WM.rewind dk (W 12)) (.seq (WM.rewind dt (W 13))
    (writeReqM true true true dc dk dt o (eR.trans W)))))

/-- **The codec's round trip**: parsing `frame req.word` and writing the parsed fields gives `frame req.word` again,
with the values `n`, `a` and the mode bit recovered. -/
theorem roundTrip_spec (s dc dk dt o : Fin (ns + 1)) (hsc : s ≠ dc) (hsk : s ≠ dk) (hst' : s ≠ dt) (hso : s ≠ o)
    (hck : dc ≠ dk) (hct : dc ≠ dt) (hco : dc ≠ o) (hkt : dk ≠ dt) (hko : dk ≠ o) (hto : dt ≠ o)
    (W : Fin 14 ↪ Fin nr) (r : PrimRequest) (pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st s = pre ++ marks r.word ++ rest) (hsh : σ.sh s = pre.length)
    (hc : σ.st dc = []) (hcs : σ.sh dc = 0) (hk : σ.st dk = []) (hks : σ.sh dk = 0)
    (ht : σ.st dt = []) (hts : σ.sh dt = 0) (ho : σ.sh o = (σ.st o).length) (hz : ∀ i : Fin 14, σ.val (W i) = 0)
    (hcap : 3 * (RepairOrdinary.frame r.word).length + 8 * r.n + 8 * r.a + 8 * (carrierCodes r).length +
      8 * r.translation.length + 100 ≤ cap) :
    ∃ τ cost, WExec cap (roundTripM s dc dk dt o W) σ τ cost ∧ τ.st o = σ.st o ++ RepairOrdinary.frame r.word ∧
      τ.val (W 0) = r.n ∧ τ.val (W 1) = r.a ∧ decide (τ.val (W 2) ≠ 0) = modeBit r.mode := by
  have hfl : (RepairOrdinary.frame r.word).length = 2 * r.word.length + 1 := by rw [RepairOrdinary.frame_length]
  have hwl := word_length r
  have q1 := parseReqM_spec cap s dc dk dt hsc hsk hst' hck hct hkt W r pre rest σ hst hsh
    (by rw [hcs, hc]; rfl) (by rw [hks, hk]; rfl) (by rw [hts, ht]; rfl)
    (fun i _ _ _ => hz i) (by rw [hz 9, hz 12, hz 13]; omega)
  set P := (((((appendO (appendO (appendO σ dc (W 9) (marks ((codeList r).flatMap RepairRepresentation.natWord)))
    dk (W 12) (marks (RepairRepresentation.natListWord (carrierCodes r)))) dt (W 13)
      (marks (RepairRepresentation.natListWord r.translation))).seth s (pre.length + 2 * r.word.length)).setv
        (W 0) r.n).setv (W 1) r.a).setv (W 2) (modeBit r.mode).toNat) with hP
  -- rewind the three field streams
  have hP9 : P.val (W 9) = 2 * ((codeList r).flatMap RepairRepresentation.natWord).length := by
    simp [P, Function.update_apply, Wne14 W (show (9 : Fin 14) ≠ 2 by decide),
      Wne14 W (show (9 : Fin 14) ≠ 1 by decide), Wne14 W (show (9 : Fin 14) ≠ 0 by decide),
      Wne14 W (show (9 : Fin 14) ≠ 13 by decide), Wne14 W (show (9 : Fin 14) ≠ 12 by decide), hz 9]
  have q2 := wrewind_spec cap dc (W 9) _ P hP9 (by rw [hP9]; omega)
  set P2 := (P.setv (W 9) 0).seth dc (P.sh dc - 2 * ((codeList r).flatMap RepairRepresentation.natWord).length) with hP2
  have hP212 : P2.val (W 12) = 2 * (RepairRepresentation.natListWord (carrierCodes r)).length := by
    simp [P2, P, Function.update_apply, Wne14 W (show (12 : Fin 14) ≠ 9 by decide),
      Wne14 W (show (12 : Fin 14) ≠ 2 by decide), Wne14 W (show (12 : Fin 14) ≠ 1 by decide),
      Wne14 W (show (12 : Fin 14) ≠ 0 by decide), Wne14 W (show (12 : Fin 14) ≠ 13 by decide), hz 12]
  have q3 := wrewind_spec cap dk (W 12) _ P2 hP212 (by rw [hP212]; omega)
  set P3 := (P2.setv (W 12) 0).seth dk (P2.sh dk - 2 * (RepairRepresentation.natListWord (carrierCodes r)).length)
    with hP3
  have hP313 : P3.val (W 13) = 2 * (RepairRepresentation.natListWord r.translation).length := by
    simp [P3, P2, P, Function.update_apply, Wne14 W (show (13 : Fin 14) ≠ 12 by decide),
      Wne14 W (show (13 : Fin 14) ≠ 9 by decide), Wne14 W (show (13 : Fin 14) ≠ 2 by decide),
      Wne14 W (show (13 : Fin 14) ≠ 1 by decide), Wne14 W (show (13 : Fin 14) ≠ 0 by decide), hz 13]
  have q4 := wrewind_spec cap dt (W 13) _ P3 hP313 (by rw [hP313]; omega)
  set P4 := (P3.setv (W 13) 0).seth dt (P3.sh dt - 2 * (RepairRepresentation.natListWord r.translation).length)
    with hP4
  -- write
  have hR : ∀ i : Fin 12, (eR.trans W) i = W (Fin.castLE (by norm_num) i) := fun i => rfl
  have hP4v : ∀ i : Fin 14, P4.val (W i) =
      if i = 0 then r.n else if i = 1 then r.a else if i = 2 then (modeBit r.mode).toNat else 0 := by
    intro i
    fin_cases i <;> simp [P4, P3, P2, P, Function.update_apply, Wne14 W, hz]
  have q5 := writeReqM_spec cap true true true dc dk dt o hco hko hto hck hct hkt (eR.trans W) r [] [] [] [] [] [] P4
    (by simp [P4, P3, P2, P, Function.update_apply, hck, hct, Ne.symm hsc, hc, ParseNat.enc])
    (by simp [P4, P3, P2, P, Function.update_apply, hck, hct, Ne.symm hsc, hcs, RepairOrdinary.Streaming.marks_length])
    (by simp [P4, P3, P2, P, Function.update_apply, hkt, Ne.symm hck, Ne.symm hsk, hk, ParseNat.enc])
    (by simp [P4, P3, P2, P, Function.update_apply, hkt, Ne.symm hck, Ne.symm hsk, hks,
      RepairOrdinary.Streaming.marks_length])
    (by simp [P4, P3, P2, P, Function.update_apply, Ne.symm hkt, Ne.symm hct, Ne.symm hst', ht, ParseNat.enc])
    (by simp [P4, P3, P2, P, Function.update_apply, Ne.symm hkt, Ne.symm hct, Ne.symm hst', hts,
      RepairOrdinary.Streaming.marks_length])
    (by simp [P4, P3, P2, P, Function.update_apply, Ne.symm hto, Ne.symm hko, Ne.symm hco, Ne.symm hso, ho])
    (by rw [hR, hP4v]; rfl) (by rw [hR, hP4v]; rfl)
    (by rw [hR, hP4v]; cases r.mode <;> rfl)
    (by intro i h3 _
        rw [hR, hP4v]
        rw [if_neg (fun h => by have := congrArg Fin.val h; simp at this; omega),
          if_neg (fun h => by have := congrArg Fin.val h; simp at this; omega),
          if_neg (fun h => by have := congrArg Fin.val h; simp at this; omega)])
    (by rw [hR, hP4v]; simp; omega)
  refine ⟨_, _, WExec.seq q1 (WExec.seq q2 (WExec.seq q3 (WExec.seq q4 q5))), ?_, ?_, ?_, ?_⟩
  · simp [P4, P3, P2, P, Function.update_apply, Ne.symm hto, Ne.symm hko, Ne.symm hco, Ne.symm hso]
  · simp [Function.update_apply, hR, P4, P3, P2, P, Wne14 W]
  · simp [Function.update_apply, hR, P4, P3, P2, P, Wne14 W]
  · simp [Function.update_apply, hR, P4, P3, P2, P, Wne14 W]

end RoundTrip

end NearCubicWires.WireExponent3_5.PrimAsm.Codec
