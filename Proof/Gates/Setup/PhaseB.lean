import Proof.Gates.Setup.PhaseP
import Proof.Gates.Setup.Positions

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Worker (width pcpp gadgets oracleOK nu PairOK)
open NearCubicGates.Close.Worker.Format (readCount readField readBits countWord)
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (updS)

noncomputable section

/-! ## The readers do not see trailing blanks -/

theorem rd_tail {a b : List Bool} {x y : Bool} (h : RdEq (x :: a) (y :: b)) : RdEq a b := fun p => by
  have := h (p + 1); simpa [readTapeBit] using this

theorem rd_nil_tail {a : List Bool} {x : Bool} (h : RdEq [] (x :: a)) : RdEq [] a := fun p => by
  have := h (p + 1); simpa [readTapeBit] using this

theorem rd_head {a b : List Bool} {x y : Bool} (h : RdEq (x :: a) (y :: b)) : x = y := by
  have := h 0; simpa [readTapeBit] using this

theorem rd_nil_head {a : List Bool} {x : Bool} (h : RdEq [] (x :: a)) : x = false := by
  have := h 0; simpa [readTapeBit] using this.symm

theorem rc_rd : ∀ (a b : List Bool), RdEq a b →
    (readCount a).1 = (readCount b).1 ∧ RdEq (readCount a).2 (readCount b).2
  | [], [], _ => ⟨rfl, RdEq.refl _⟩
  | [], x :: r, h => by
    have hx := rd_nil_head h
    subst hx
    exact ⟨rfl, rd_nil_tail h⟩
  | x :: r, [], h => by
    have hx := rd_nil_head (RdEq.symm h)
    subst hx
    exact ⟨rfl, RdEq.symm (rd_nil_tail (RdEq.symm h))⟩
  | x :: a, y :: b, h => by
    have hxy := rd_head h
    subst hxy
    cases x with
    | false => exact ⟨rfl, rd_tail h⟩
    | true =>
      have ih := rc_rd a b (rd_tail h)
      simp only [readCount]
      exact ⟨by rw [ih.1], ih.2⟩

theorem drop_rd (n : ℕ) {a b : List Bool} (h : RdEq a b) : RdEq (a.drop n) (b.drop n) := fun p => by
  have := h (n + p)
  simpa [readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_drop] using this

theorem rb_rd (ℓ : ℕ) {a b : List Bool} (h : RdEq a b) :
    (readBits ℓ a).1 = (readBits ℓ b).1 ∧ RdEq (readBits ℓ a).2 (readBits ℓ b).2 := by
  refine ⟨?_, drop_rd ℓ h⟩
  unfold readBits
  simp only
  congr 1
  funext i
  exact h i.val

theorem rf_rd {a b : List Bool} (h : RdEq a b) :
    (readField a).1 = (readField b).1 ∧ RdEq (readField a).2 (readField b).2 := by
  obtain ⟨h1, h2⟩ := rc_rd a b h
  unfold readField
  rw [h1]
  exact rb_rd _ h2

theorem oracleEnd_rd {a b : List Bool} (h : RdEq a b) : oracleEnd a = oracleEnd b := by
  unfold oracleEnd; rw [(rc_rd a b h).1]

theorem pairEnd_rd {a b : List Bool} (h : RdEq a b) : pairEnd a = pairEnd b := by
  unfold pairEnd
  rw [oracleEnd_rd h, oracleEnd_rd (drop_rd (oracleEnd b) h)]

/-! ## The ideal guess word of phase B -/

/-- The padding of the ideal guess word of phase B. -/
def padB (N pad : ℕ) : ℕ := pad + 2 * (N / 16) + 4

theorem guessWord_padB (N : ℕ) (bits : List Bool) (pad : ℕ) :
    guessWord N bits (padB N pad) = guessWord N bits pad ++ List.replicate (2 * (N / 16) + 4) false := by
  unfold guessWord padB
  rw [List.append_assoc, ← List.replicate_add, Nat.add_assoc]

theorem guessWord_padB_rd (N : ℕ) (bits : List Bool) (pad : ℕ) :
    RdEq (guessWord N bits (padB N pad)) (guessWord N bits pad) := by
  rw [guessWord_padB]
  exact rdEq_append_blank _ _ (fun b hb => (List.mem_replicate.1 hb).2)

theorem guessWord_length (N : ℕ) (bits : List Bool) (pad : ℕ) : (guessWord N bits pad).length = N / 16 + pad := by
  simp [guessWord, prefixBits_length]

/-- A field at the start of `r` is physical when `r` contains a blank and is long enough. -/
theorem field_split (r : List Bool) (hf : false ∈ r) (hl : 2 * (readCount r).1 + 1 ≤ r.length) :
    r = countWord (readField r).1.length ++ (readField r).1 ++ (readField r).2 ∧
      (readField r).1.length = (readCount r).1 ∧ (readField r).2 = r.drop (2 * (readCount r).1 + 1) := by
  set l := (readCount r).1 with hl'
  set t := (readCount r).2 with ht
  have hsplit : r = countWord l ++ t := readCount_split r hf
  have htl : l ≤ t.length := by
    have := congrArg List.length hsplit
    simp [countWord] at this
    omega
  have hrf : readField r = (t.take l, t.drop l) := by
    unfold readField readBits
    rw [← hl', ← ht, ofFn_getD_take t l htl]
  have hlen : (t.take l).length = l := by simp; omega
  refine ⟨?_, by rw [hrf, hlen], Worker.Format.readField_snd r⟩
  rw [hrf, hlen]
  simp only
  rw [List.append_assoc, List.take_append_drop]
  exact hsplit

/-- **The first field of the ideal guess word is physical.** -/
theorem field1_split (N : ℕ) (bits : List Bool) (pad : ℕ) :
    guessWord N bits (padB N pad) = countWord (readField (guessWord N bits (padB N pad))).1.length ++
        (readField (guessWord N bits (padB N pad))).1 ++ (readField (guessWord N bits (padB N pad))).2 ∧
      (readField (guessWord N bits (padB N pad))).1.length ≤ N / 16 ∧
      (readField (guessWord N bits (padB N pad))).2 =
        (guessWord N bits (padB N pad)).drop (oracleEnd (guessWord N bits (padB N pad))) := by
  obtain ⟨h1, h2, h3, h4⟩ := guessWord_split N bits (padB N pad) (by unfold padB; omega)
  exact ⟨h1, by omega, h4⟩

theorem drop_guessWord (N : ℕ) (bits : List Bool) (pad p : ℕ) :
    ∃ l m, (guessWord N bits pad).drop p = l ++ List.replicate m false ∧ l.length ≤ N / 16 ∧
      m + p ≥ pad := by
  unfold guessWord
  refine ⟨(Codec.prefixBits bits (N / 16)).drop p, pad - (p - (Codec.prefixBits bits (N / 16)).length), ?_, ?_, ?_⟩
  · rw [List.drop_append, List.drop_replicate]
  · simp [prefixBits_length]
  · rw [prefixBits_length]; omega

/-- **The second field of the ideal guess word is physical.** -/
theorem field2_split (N : ℕ) (bits : List Bool) (pad : ℕ) (hpad : N / 16 + 1 ≤ pad) :
    let r := (readField (guessWord N bits (padB N pad))).2
    r = countWord (readField r).1.length ++ (readField r).1 ++ (readField r).2 ∧ (readField r).1.length ≤ N / 16 ∧
      oracleEnd r = 2 * (readField r).1.length + 1 := by
  intro r
  obtain ⟨-, hl1, hr1⟩ := field1_split N bits pad
  have hp1 : oracleEnd (guessWord N bits (padB N pad)) ≤ 2 * (N / 16) + 1 := by
    have := (guessWord_split N bits (padB N pad) (by unfold padB; omega)).2.2.1
    unfold oracleEnd; omega
  obtain ⟨l, m, hlm, hll, hm⟩ := drop_guessWord N bits (padB N pad) (oracleEnd (guessWord N bits (padB N pad)))
  have hr : r = l ++ List.replicate m false := by rw [← hlm]; exact hr1
  have hc : (readCount r).1 ≤ N / 16 := by rw [hr]; exact (readCount_pad l m).trans hll
  have hpB : padB N pad = pad + 2 * (N / 16) + 4 := rfl
  have hm4 : 1 ≤ m := by omega
  have hf : false ∈ r := by
    rw [hr]; apply List.mem_append_right; apply List.mem_replicate.2; exact ⟨by omega, rfl⟩
  have hrl : r.length = (guessWord N bits (padB N pad)).length - oracleEnd (guessWord N bits (padB N pad)) := by
    have hr1' : r = List.drop (oracleEnd (guessWord N bits (padB N pad))) (guessWord N bits (padB N pad)) := hr1
    rw [hr1', List.length_drop]
  have hlen : 2 * (readCount r).1 + 1 ≤ r.length := by
    rw [hrl, guessWord_length]; omega
  obtain ⟨hs, hl2, -⟩ := field_split r hf hlen
  exact ⟨hs, by omega, by unfold oracleEnd; omega⟩

/-- The fields and positions of the ideal guess word are those of the guess word. -/
theorem fields_padB (N : ℕ) (bits : List Bool) (pad : ℕ) :
    (readField (guessWord N bits (padB N pad))).1 = (readField (guessWord N bits pad)).1 ∧
      (readField (readField (guessWord N bits (padB N pad))).2).1 =
        (readField (readField (guessWord N bits pad)).2).1 ∧
      pairEnd (guessWord N bits (padB N pad)) = pairEnd (guessWord N bits pad) := by
  have h := guessWord_padB_rd N bits pad
  obtain ⟨e1, r1⟩ := rf_rd h
  exact ⟨e1, (rf_rd r1).1, pairEnd_rd h⟩

/-! ## `updS` frames -/

theorem updS_sh_zero {ns nr t : ℕ} (tmap : Fin t → Fin (ns + 1)) (hinj : Function.Injective tmap) (σ : WState ns nr)
    (tout : Fin t → List Bool) (i : Fin (ns + 1)) :
    (updS tmap σ (fun _ => 0) tout).sh i = if ∃ j, tmap j = i then 0 else σ.sh i := by
  classical
  by_cases h : ∃ j, tmap j = i
  · obtain ⟨j, rfl⟩ := h
    rw [updS_sh_slot tmap σ _ tout hinj j, if_pos ⟨j, rfl⟩]
  · rw [if_neg h, updS_sh_other tmap σ _ tout i (fun j hj => h ⟨j, hj⟩)]

theorem notIn {ns t : ℕ} (m : Fin t → Fin (ns + 1)) (i : Fin (ns + 1)) (h : ∀ j, (m j).val ≠ i.val) : ∀ j, m j ≠ i :=
  fun j e => h j (congrArg Fin.val e)

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams}

/-! ## The program -/

section Prog
variable (D : SetupData s P g) (W : OuterM.WidthDonor s.mw (g.sv s))

def wdP (p : Program) (tmap : Fin p.tapeCount → Fin (nsW D + 1)) : WMX (nsW D) nrW :=
  .seq (.wm (Codec.copyRW (sX D) (tmap (Worker.inTape p)) tW gU gK)) (WMX.machZ p.machine tmap (sL D))

/-- `FL := [f₁ ∧ f₂]` from the two decoders' flags (`FL` holds `[true]`). -/
def flagB : WMX (nsW D) nrW :=
  .ifs (sF1 D W) (.ifs (sF2 D W) WMX.skip (WMX.wr (sFL D) false)) (WMX.wr (sFL D) false)

/-- **Phase B.** -/
def phB : WMX (nsW D) nrW :=
  .seq (wdP D (Worker.wdB W) (mW1 D W)) (.seq (wdP D (Worker.wdU W) (mU1 D W))
  (.seq (wdP D (Worker.wdB W) (mW2 D W)) (.seq (wdP D (Worker.wdU W) (mU2 D W))
  (.seq (.wm (Codec.unaryQ (mU1 D W (oU W)) (regE 6) gU gK))
  (.seq (Worker.oracleP (sX D) (sWT D) (sL D) (mO1 D W) tW gU gK gT)
  (.seq (Worker.oracleP (sX D) (sWT D) (sL D) (mO2 D W) tW gU gK gT) (flagB D W)))))))

end Prog

/-! ## The states before and after phase B -/

structure PreB (D : SetupData s P g) {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ)
    (ι : WState (nsW D) nrW) : Prop where
  x : ι.st (sX D) = RepairOrdinary.frame (List.ofFn x)
  bw : ι.st (sBW D) = RepairOrdinary.frame bits
  wt : ι.st (sWT D) = guessWord N bits pad
  fl : ι.st (sFL D) = [true]
  blank : ∀ i : Fin (nsW D + 1), i.val ≠ 0 → i.val ≠ 1 → i.val ≠ 2 → i.val ≠ 16 → ι.st i = []
  sh : ∀ i, ι.sh i = 0
  val : ι.val = fun r => if r = rN then N else if r = rNu then nu N else 0
  cell : ι.cell = false

structure AfterB (D : SetupData s P g) (W : OuterM.WidthDonor s.mw (g.sv s)) {N : ℕ} (x : BitInput N)
    (bits : List Bool) (pad : ℕ) (ι : WState (nsW D) nrW) : Prop where
  x : ι.st (sX D) = RepairOrdinary.frame (List.ofFn x)
  bw : ι.st (sBW D) = RepairOrdinary.frame bits
  wt : ι.st (sWT D) = guessWord N bits pad
  fl : ι.st (sFL D) = [oracleOK s g N (guessWord N bits pad)]
  d1 : ∀ c : BooleanCircuit (width s g N),
    decodeBooleanCircuit (width s g N) (value (readField (guessWord N bits pad)).1) = some c →
    ι.st (sD1 D W) = PCPPNative.descriptor c
  d2 : ∀ c : BooleanCircuit (width s g N),
    decodeBooleanCircuit (width s g N) (value (readField (readField (guessWord N bits pad)).2).1) = some c →
    ι.st (sD2 D W) = PCPPNative.descriptor c
  blank : ∀ i : Fin (nsW D + 1), i.val ≠ 0 → i.val ≠ 1 → i.val ≠ 2 → i.val ≠ 16 →
    (i.val < 21 ∨ 21 + 2 * tWB W + 2 * tWU W + 2 * tO ≤ i.val) → ι.st i = []
  sh : ι.sh = fun i => if i = sWT D then pairEnd (guessWord N bits pad) else 0
  val : ι.val = fun r => if r = regE 6 then width s g N else if r = rN then N else if r = rNu then nu N else 0
  cell : ι.cell = false

def fdCost (n b : ℕ) : ℕ :=
  22 * n + 1 + 1 + 7 + 1 + (18 * (2 * n + 1) + 3 + 1 + (5 * (2 * n + 1) + 1 + 1 + (5 * (2 * n + 1) + 1))) + 1 +
    (2 * b + 2)

/-- The cost of phase B. -/
def costB (W : OuterM.WidthDonor s.mw (g.sv s)) {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) : ℕ :=
  4 * fdCost N (2 * (W.K * (N + 1) ^ 1) + 2) + 50 * (width s g N + 2) +
    Worker.oracleCost (List.ofFn x) (readField (guessWord N bits pad)).1 (width s g N).bits +
    Worker.oracleCost (List.ofFn x) (readField (readField (guessWord N bits pad)).2).1 (width s g N).bits + 20

/-! ## The flag step -/

theorem flagB_exec (D : SetupData s P g) (W : OuterM.WidthDonor s.mw (g.sv s)) {cap : ℕ} (σ : WState (nsW D) nrW)
    (b1 b2 : Bool) (hf1 : σ.st (sF1 D W) = [b1]) (hf1h : σ.sh (sF1 D W) = 0) (hf2 : σ.st (sF2 D W) = [b2])
    (hf2h : σ.sh (sF2 D W) = 0) (hFL : σ.st (sFL D) = [true]) (hFLh : σ.sh (sFL D) = 0) :
    WXExec cap (flagB D W) σ (σ.sets (sFL D) [b1 && b2]) 3 := by
  have w1 : wbit σ (sF1 D W) = b1 := by unfold wbit; rw [hf1, hf1h]; rfl
  have w2 : wbit σ (sF2 D W) = b2 := by unfold wbit; rw [hf2, hf2h]; rfl
  have hwr : σ.sets (sFL D) (writeTapeBit (σ.st (sFL D)) (σ.sh (sFL D)) false) = σ.sets (sFL D) [false] := by
    rw [hFL, hFLh]; rfl
  have hid : σ = σ.sets (sFL D) [true] := by
    apply WState.eq <;> try rfl
    funext i; by_cases hi : i = sFL D
    · subst hi; simp [hFL]
    · simp [Function.update_of_ne hi]
  cases b1 <;> cases b2
  · exact WXExec.cast cap (WXExec.ifsF w1 (WXExec.wr (cap := cap) (sFL D) false σ)) (by rw [hwr]; rfl) (by omega)
  · exact WXExec.cast cap (WXExec.ifsF w1 (WXExec.wr (cap := cap) (sFL D) false σ)) (by rw [hwr]; rfl) (by omega)
  · exact WXExec.cast cap (WXExec.ifsT w1 (WXExec.ifsF w2 (WXExec.wr (cap := cap) (sFL D) false σ)))
      (by rw [hwr]; rfl) (by omega)
  · exact WXExec.cast cap (WXExec.ifsT w1 (WXExec.ifsT w2 (WXExec.skip cap σ))) hid (by omega)

/-! ## Phase B on the ideal state -/

theorem phB_ideal (D : SetupData s P g) (W : OuterM.WidthDonor s.mw (g.sv s)) (R : OuterM.ARun s.mw (g.sv s))
    (hL : Lay D W R) {N : ℕ} (x : BitInput N) (bits : List Bool) (pad cap : ℕ) (hpad : N / 16 + 1 ≤ pad)
    (hN : D.N0 ≤ N) (hpow : N = 2 ^ nu N) (hcap : 8 * N + 4 * width s g N + 8 ≤ cap) (ι0 : WState (nsW D) nrW)
    (h0 : PreB D x bits pad ι0) :
    ∃ τ ι, WXExec cap (phB D W) ι0 τ (costB W x bits pad) ∧ SimW ι τ ∧ AfterB D W x bits pad ι := by
  classical
  obtain ⟨hN4, hqb⟩ := D.hN0 N hN
  -- the fields of the ideal guess word
  obtain ⟨hs1, hl1, hr1⟩ := field1_split N bits pad
  obtain ⟨hs2, hl2, ho2⟩ := field2_split N bits pad hpad
  obtain ⟨ef1, ef2, epe⟩ := fields_padB N bits pad
  have hgs := (guessWord_split N bits (padB N pad) (by unfold padB; omega)).2.1
  have hq : OuterM.qOf s.mw (g.sv s) N = width s g N := by
    have := OuterM.qOf_two_pow s.mw (g.sv s) (nu N)
    rw [← hpow] at this; exact this
  have hvq : value (width s g N).bits = width s g N := LitDecode.value_bits _
  set w := guessWord N bits pad with hw
  set wp := guessWord N bits (padB N pad) with hwp
  set q := width s g N with hqdef
  set f1 := (readField wp).1 with hf1
  set r1 := (readField wp).2 with hr1d
  set f2 := (readField r1).1 with hf2
  set r2 := (readField r1).2 with hr2d
  have vFL := sFL_val hL
  have htO := tO_eq
  have hoB := (oB W).isLt
  have hoU := (oU W).isLt
  have hA := tA_eq hL
  have hnsW : nsW D = 15 + D.tA + D.cf.t + D.tc + 46 := rfl
  have hp1 : oracleEnd wp = 2 * f1.length + 1 := by
    unfold oracleEnd; omega
  have hpe : pairEnd wp = 2 * f1.length + 1 + (2 * f2.length + 1) := by
    unfold pairEnd
    rw [← hr1, ho2, hp1]
  -- 0. the ideal start: the guess word with the extra blanks
  set ι0' := ι0.sets (sWT D) wp with hι0'
  have s0 : SimW ι0' ι0 := CheckedPCPP.SimW.symm (Worker.simW_sets ι0 (sWT D) wp (by
    rw [h0.wt]; exact RdEq.symm (guessWord_padB_rd N bits pad)))
  have st0 : ∀ i, i ≠ sWT D → ι0'.st i = ι0.st i := fun i hi => by simp [hι0', Function.update_of_ne hi]
  have b0 : ∀ i : Fin (nsW D + 1), i.val ≠ 0 → i.val ≠ 1 → i.val ≠ 2 → i.val ≠ 16 → ι0'.st i = [] := fun i h1 h2 h3 h4 =>
    by rw [st0 i (fin_ne_of_val (by show i.val ≠ 2; exact h3))]; exact h0.blank i h1 h2 h3 h4
  have sh0 : ∀ i, ι0'.sh i = 0 := fun i => by simp [hι0', h0.sh]
  have z0 : ∀ r, r ≠ rN → r ≠ rNu → ι0'.val r = 0 := fun r h1 h2 => by simp [hι0', h0.val, h1, h2]
  have X0 : ι0'.st (sX D) = RepairOrdinary.frame (List.ofFn x) ++ [] := by
    rw [st0 _ (fin_ne_of_val (by simp [sX, sWT, fixS])), h0.x, List.append_nil]
  -- 1–4. the width donors
  obtain ⟨o1, r1', ho1⟩ := Worker.widthB_ready W x
  obtain ⟨o2, r2', ho2'⟩ := Worker.widthU_ready W x
  obtain ⟨o3, r3', ho3⟩ := Worker.widthB_ready W x
  obtain ⟨o4, r4', ho4⟩ := Worker.widthU_ready W x
  rw [hq] at ho1 ho2' ho3 ho4
  have hXn : ∀ (t : ℕ) (m : Fin t → Fin (nsW D + 1)), (∀ j, 21 ≤ (m j).val) → ∀ j, m j ≠ sX D :=
    fun t m h j e => by have := h j; rw [e] at this; simp [sX, fixS] at this
  have hLn : ∀ (t : ℕ) (m : Fin t → Fin (nsW D + 1)), (∀ j, 21 ≤ (m j).val) → ∀ j, m j ≠ sL D :=
    fun t m h j e => by have := h j; rw [e] at this; simp [sL, fixS] at this
  have hWn : ∀ (t : ℕ) (m : Fin t → Fin (nsW D + 1)), (∀ j, 21 ≤ (m j).val) → ∀ j, m j ≠ sWT D :=
    fun t m h j e => by have := h j; rw [e] at this; simp [sWT, fixS] at this
  have g1 : ∀ j, 21 ≤ (mW1 D W j).val := fun j => by rw [mW1_val hL]; omega
  have g2 : ∀ j, 21 ≤ (mU1 D W j).val := fun j => by rw [mU1_val hL]; omega
  have g3 : ∀ j, 21 ≤ (mW2 D W j).val := fun j => by rw [mW2_val hL]; omega
  have g4 : ∀ j, 21 ≤ (mU2 D W j).val := fun j => by rw [mU2_val hL]; omega
  have g5 : ∀ j, 21 ≤ (mO1 D W j).val := fun j => by rw [mO1_val hL]; split_ifs <;> omega
  have g6 : ∀ j, 21 ≤ (mO2 D W j).val := fun j => by rw [mO2_val hL]; split_ifs <;> omega
  have hLb : ∀ (σ : WState (nsW D) nrW), σ.st (sL D) = [] → Worker.Blank (σ.st (sL D)) := fun σ h p => by
    rw [h]; rfl
  have bL : ι0'.st (sL D) = [] := b0 _ (by simp [sL, fixS]) (by simp [sL, fixS]) (by simp [sL, fixS])
    (by simp [sL, fixS])
  obtain ⟨τ1, e1, s1⟩ := Worker.frameDonor_ideal (Worker.wdB W).machine _ (Worker.inTape (Worker.wdB W))
    (List.ofFn x) o1 r1' (cap := cap) (mW1 D W) (mW1_inj hL) (sX D) (sL D) (hXn _ _ g1) (hLn _ _ g1) tW gU gK
    (by decide) (by decide) (by decide) [] ι0' X0 (sh0 _)
    (fun j => b0 _ (by have := g1 j; omega) (by have := g1 j; omega) (by have := g1 j; omega)
      (by have := g1 j; omega)) (fun j => sh0 _) (z0 _ (by decide) (by decide)) (z0 _ (by decide) (by decide))
    (z0 _ (by decide) (by decide)) (by simp; omega) (hLb _ bL) (sh0 _)
  set ι1 := updS (mW1 D W) ι0' (fun _ => 0) o1 with hι1
  have st1 : ∀ i : Fin (nsW D + 1), (i.val < 21 ∨ 21 + tWB W ≤ i.val) → ι1.st i = ι0'.st i := fun i hi =>
    updS_st_other _ _ _ _ i (notIn _ _ (fun j => by rw [mW1_val hL]; omega))
  have sh1 : ∀ i, ι1.sh i = 0 := fun i => by rw [hι1, updS_sh_zero _ (mW1_inj hL)]; split_ifs <;> simp [sh0]
  obtain ⟨τ2, e2, s2⟩ := Worker.frameDonor_ideal (Worker.wdU W).machine _ (Worker.inTape (Worker.wdU W))
    (List.ofFn x) o2 r2' (cap := cap) (mU1 D W) (mU1_inj hL) (sX D) (sL D) (hXn _ _ g2) (hLn _ _ g2) tW gU gK
    (by decide) (by decide) (by decide) [] ι1 (by rw [st1 _ (by simp [sX, fixS])]; exact X0) (sh1 _)
    (fun j => by
      have := mU1_val hL j
      rw [st1 _ (by omega)]
      exact b0 _ (by omega) (by omega) (by omega) (by omega)) (fun j => sh1 _)
    (z0 _ (by decide) (by decide)) (z0 _ (by decide) (by decide)) (z0 _ (by decide) (by decide)) (by simp; omega)
    (hLb _ (by rw [st1 _ (by simp [sL, fixS])]; exact bL)) (sh1 _)
  set ι2 := updS (mU1 D W) ι1 (fun _ => 0) o2 with hι2
  have st2 : ∀ i : Fin (nsW D + 1), (i.val < 21 ∨ 21 + tWB W + tWU W ≤ i.val) → ι2.st i = ι0'.st i := fun i hi => by
    rw [hι2, updS_st_other _ _ _ _ i (notIn _ _ (fun j => by rw [mU1_val hL]; omega)), st1 i (by omega)]
  have sh2 : ∀ i, ι2.sh i = 0 := fun i => by rw [hι2, updS_sh_zero _ (mU1_inj hL)]; split_ifs <;> simp [sh1]
  obtain ⟨τ3, e3, s3⟩ := Worker.frameDonor_ideal (Worker.wdB W).machine _ (Worker.inTape (Worker.wdB W))
    (List.ofFn x) o3 r3' (cap := cap) (mW2 D W) (mW2_inj hL) (sX D) (sL D) (hXn _ _ g3) (hLn _ _ g3) tW gU gK
    (by decide) (by decide) (by decide) [] ι2 (by rw [st2 _ (by simp [sX, fixS])]; exact X0) (sh2 _)
    (fun j => by
      have := mW2_val hL j
      rw [st2 _ (by omega)]
      exact b0 _ (by omega) (by omega) (by omega) (by omega)) (fun j => sh2 _)
    (z0 _ (by decide) (by decide)) (z0 _ (by decide) (by decide)) (z0 _ (by decide) (by decide)) (by simp; omega)
    (hLb _ (by rw [st2 _ (by simp [sL, fixS])]; exact bL)) (sh2 _)
  set ι3 := updS (mW2 D W) ι2 (fun _ => 0) o3 with hι3
  have st3 : ∀ i : Fin (nsW D + 1), (i.val < 21 ∨ 21 + 2 * tWB W + tWU W ≤ i.val) → ι3.st i = ι0'.st i :=
    fun i hi => by
      rw [hι3, updS_st_other _ _ _ _ i (notIn _ _ (fun j => by rw [mW2_val hL]; omega)), st2 i (by omega)]
  have sh3 : ∀ i, ι3.sh i = 0 := fun i => by rw [hι3, updS_sh_zero _ (mW2_inj hL)]; split_ifs <;> simp [sh2]
  obtain ⟨τ4, e4, s4⟩ := Worker.frameDonor_ideal (Worker.wdU W).machine _ (Worker.inTape (Worker.wdU W))
    (List.ofFn x) o4 r4' (cap := cap) (mU2 D W) (mU2_inj hL) (sX D) (sL D) (hXn _ _ g4) (hLn _ _ g4) tW gU gK
    (by decide) (by decide) (by decide) [] ι3 (by rw [st3 _ (by simp [sX, fixS])]; exact X0) (sh3 _)
    (fun j => by
      have := mU2_val hL j
      rw [st3 _ (by omega)]
      exact b0 _ (by omega) (by omega) (by omega) (by omega)) (fun j => sh3 _)
    (z0 _ (by decide) (by decide)) (z0 _ (by decide) (by decide)) (z0 _ (by decide) (by decide)) (by simp; omega)
    (hLb _ (by rw [st3 _ (by simp [sL, fixS])]; exact bL)) (sh3 _)
  set ι4 := updS (mU2 D W) ι3 (fun _ => 0) o4 with hι4
  have st4 : ∀ i : Fin (nsW D + 1), (i.val < 21 ∨ 21 + 2 * tWB W + 2 * tWU W ≤ i.val) → ι4.st i = ι0'.st i :=
    fun i hi => by
      rw [hι4, updS_st_other _ _ _ _ i (notIn _ _ (fun j => by rw [mU2_val hL]; omega)), st3 i (by omega)]
  have sh4 : ∀ i, ι4.sh i = 0 := fun i => by rw [hι4, updS_sh_zero _ (mU2_inj hL)]; split_ifs <;> simp [sh3]
  -- the donors' outputs
  have oW1 : ι4.st (mW1 D W (oB W)) = RepairOrdinary.frame q.bits := by
    have := mW1_val hL (oB W)
    rw [hι4, updS_st_other _ _ _ _ _ (notIn _ _ (fun j => by rw [mU2_val hL]; omega)), hι3,
      updS_st_other _ _ _ _ _ (notIn _ _ (fun j => by rw [mW2_val hL]; omega)), hι2,
      updS_st_other _ _ _ _ _ (notIn _ _ (fun j => by rw [mU1_val hL]; omega)), hι1,
      updS_st_slot _ _ _ _ (mW1_inj hL)]
    exact ho1
  have oU1 : ι4.st (mU1 D W (oU W)) = List.replicate q true := by
    have := mU1_val hL (oU W)
    rw [hι4, updS_st_other _ _ _ _ _ (notIn _ _ (fun j => by rw [mU2_val hL]; omega)), hι3,
      updS_st_other _ _ _ _ _ (notIn _ _ (fun j => by rw [mW2_val hL]; omega)), hι2,
      updS_st_slot _ _ _ _ (mU1_inj hL)]
    exact ho2'
  have oW2 : ι4.st (mW2 D W (oB W)) = RepairOrdinary.frame q.bits := by
    have := mW2_val hL (oB W)
    rw [hι4, updS_st_other _ _ _ _ _ (notIn _ _ (fun j => by rw [mU2_val hL]; omega)), hι3,
      updS_st_slot _ _ _ _ (mW2_inj hL)]
    exact ho3
  have oU2 : ι4.st (mU2 D W (oU W)) = List.replicate q true := by
    rw [hι4, updS_st_slot _ _ _ _ (mU2_inj hL)]
    exact ho4
  -- 5. `R 6 := q`
  have e5 := Codec.unaryQ_spec cap (mU1 D W (oU W)) (regE 6) gU gK (by decide) (by decide) (by decide) q ι4 oU1
    (sh4 _) (by simp [hι4, hι3, hι2, hι1]; exact z0 _ (by decide) (by decide))
    (by simp [hι4, hι3, hι2, hι1]; exact z0 _ (by decide) (by decide))
    (by simp [hι4, hι3, hι2, hι1]; exact z0 _ (by decide) (by decide)) (by omega)
  set ι5 := ι4.setv (regE 6) q with hι5
  have st5 : ∀ i, ι5.st i = ι4.st i := fun i => rfl
  -- 6. the first field: `B_src`
  have hO1_2 : mO1 D W 2 = mW1 D W (oB W) := by unfold mO1; rw [if_pos (by decide)]
  have hO1_3 : mO1 D W 3 = mU1 D W (oU W) := by unfold mO1; rw [if_neg (by decide), if_pos (by decide)]
  have hO2_2 : mO2 D W 2 = mW2 D W (oB W) := by unfold mO2; rw [if_pos (by decide)]
  have hO2_3 : mO2 D W 3 = mU2 D W (oU W) := by unfold mO2; rw [if_neg (by decide), if_pos (by decide)]
  have hrg : ([tW, gU, gK, gT] : List (Fin nrW)).Nodup := by decide
  have hO1own : ∀ j : Fin tO, j.val ≠ 2 → j.val ≠ 3 → mO1 D W j = bS D (oO1 W + j.val) := fun j h2 h3 => by
    simp [mO1, h2, h3]
  have hO2own : ∀ j : Fin tO, j.val ≠ 2 → j.val ≠ 3 → mO2 D W j = bS D (oO2 W + j.val) := fun j h2 h3 => by
    simp [mO2, h2, h3]
  obtain ⟨τ6, o5, e6, s6, hfl5, hds5⟩ := Worker.oracle_ideal (cap := cap) (sX D) (sWT D) (mW1 D W (oB W)) (mU1 D W (oU W)) (sL D)
    (mO1 D W) (mO1_inj hL) hO1_2 hO1_3 (hXn _ _ g5) (hWn _ _ g5) (hLn _ _ g5) (fin_ne_of_val (by simp [sL, sWT, fixS]))
    tW gU gK gT hrg (List.ofFn x) f1 q.bits [] [] r1 (by simp only [List.length_ofFn]; omega)
    (by simp only [List.length_ofFn]; omega) (by simp only [List.length_ofFn]; omega)
    (by simp only [List.length_ofFn]; omega) ι5 (by rw [st5, st4 _ (by simp [sX, fixS])]; exact X0) (sh4 _)
    (by
      rw [st5, st4 _ (by simp [sWT, fixS])]
      simp only [hι0', WState.sets_st, Function.update_self, List.nil_append]
      exact hs1)
    (sh4 _) (by rw [st5]; exact oW1) (by rw [st5, hvq]; exact oU1)
    (fun j h2 h3 => by
      rw [hO1own j h2 h3, st5]
      have := own1_val hL j.val j.isLt
      rw [st4 _ (by omega)]
      exact b0 _ (by omega) (by omega) (by omega) (by omega))
    (fun j => sh4 _)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [hι5, hι4, hι3, hι2, hι1] <;> exact z0 _ (by decide) (by decide))
    (hLb _ (by rw [st5, st4 _ (by simp [sL, fixS])]; exact bL)) (sh4 _)
  set ι6 := updS (mO1 D W) (ι5.seth (sWT D) ([].length + f1.length + 1 + f1.length)) (fun _ => 0) o5 with hι6
  have nO1 : ∀ i : Fin (nsW D + 1), i.val ≠ 21 + (oB W).val → i.val ≠ 21 + tWB W + (oU W).val →
      (i.val < 21 + 2 * tWB W + 2 * tWU W ∨ 21 + 2 * tWB W + 2 * tWU W + tO ≤ i.val) → ∀ j, mO1 D W j ≠ i :=
    fun i h1 h2 h3 => notIn _ _ (fun j => by rw [mO1_val hL]; split_ifs <;> omega)
  have st6 : ∀ i : Fin (nsW D + 1), i.val ≠ 21 + (oB W).val → i.val ≠ 21 + tWB W + (oU W).val →
      (i.val < 21 + 2 * tWB W + 2 * tWU W ∨ 21 + 2 * tWB W + 2 * tWU W + tO ≤ i.val) → ι6.st i = ι4.st i :=
    fun i h1 h2 h3 => by rw [hι6, updS_st_other _ _ _ _ i (nO1 i h1 h2 h3)]; rfl
  have sh6 : ∀ i, i ≠ sWT D → ι6.sh i = 0 := fun i hi => by
    rw [hι6, updS_sh_zero _ (mO1_inj hL)]; split_ifs
    · rfl
    · simp [WState.seth_sh, Function.update_of_ne hi, hι5, sh4]
  have sh6W : ι6.sh (sWT D) = f1.length + 1 + f1.length := by
    rw [hι6, updS_sh_zero _ (mO1_inj hL), if_neg (fun ⟨j, hj⟩ => hWn _ _ g5 j hj)]; simp
  have val6 : ι6.val = ι5.val := rfl
  -- 7. the second field: `B_pf`
  obtain ⟨τ7, o6, e7, s7, hfl6, hds6⟩ := Worker.oracle_ideal (cap := cap) (sX D) (sWT D) (mW2 D W (oB W))
    (mU2 D W (oU W)) (sL D) (mO2 D W) (mO2_inj hL) hO2_2 hO2_3 (hXn _ _ g6) (hWn _ _ g6) (hLn _ _ g6)
    (fin_ne_of_val (by simp [sL, sWT, fixS])) tW gU gK gT hrg (List.ofFn x) f2 q.bits []
    (countWord f1.length ++ f1) r2 (by simp only [List.length_ofFn]; omega) (by simp only [List.length_ofFn]; omega)
    (by simp only [List.length_ofFn]; omega) (by simp only [List.length_ofFn]; omega) ι6
    (by rw [st6 _ (by simp [sX, fixS] <;> omega) (by simp [sX, fixS] <;> omega) (by simp [sX, fixS] <;> omega),
      st4 _ (by simp [sX, fixS])]; exact X0)
    (sh6 _ (fin_ne_of_val (by simp [sX, sWT, fixS])))
    (by
      rw [st6 _ (by simp [sWT, fixS] <;> omega) (by simp [sWT, fixS] <;> omega) (by simp [sWT, fixS] <;> omega),
        st4 _ (by simp [sWT, fixS])]
      simp only [hι0', WState.sets_st, Function.update_self]
      rw [hs1]; nth_rw 1 [hs2]; simp [List.append_assoc])
    (by rw [sh6W]; simp [countWord]; omega)
    (by
      have := mW2_val hL (oB W)
      rw [st6 _ (by omega) (by omega) (by omega)]; exact oW2)
    (by
      have := mU2_val hL (oU W)
      rw [st6 _ (by omega) (by omega) (by omega), hvq]; exact oU2)
    (fun j h2 h3 => by
      rw [hO2own j h2 h3]
      have := own2_val hL j.val j.isLt
      rw [st6 _ (by omega) (by omega) (by omega), st4 _ (by omega)]
      exact b0 _ (by omega) (by omega) (by omega) (by omega))
    (fun j => sh6 _ (hWn _ _ g6 j))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [val6]
      rcases hr with rfl | rfl | rfl | rfl <;> simp [hι5, hι4, hι3, hι2, hι1] <;> exact z0 _ (by decide) (by decide))
    (hLb _ (by rw [st6 _ (by simp [sL, fixS] <;> omega) (by simp [sL, fixS] <;> omega) (by simp [sL, fixS] <;> omega),
      st4 _ (by simp [sL, fixS])]; exact bL))
    (sh6 _ (fin_ne_of_val (by simp [sL, sWT, fixS])))
  set ι7 := updS (mO2 D W) (ι6.seth (sWT D) ((countWord f1.length ++ f1).length + f2.length + 1 + f2.length))
    (fun _ => 0) o6 with hι7
  have nO2 : ∀ i : Fin (nsW D + 1), i.val ≠ 21 + tWB W + tWU W + (oB W).val →
      i.val ≠ 21 + 2 * tWB W + tWU W + (oU W).val →
      (i.val < 21 + 2 * tWB W + 2 * tWU W + tO ∨ 21 + 2 * tWB W + 2 * tWU W + 2 * tO ≤ i.val) → ∀ j, mO2 D W j ≠ i :=
    fun i h1 h2 h3 => notIn _ _ (fun j => by rw [mO2_val hL]; split_ifs <;> omega)
  have st7 : ∀ i : Fin (nsW D + 1), i.val ≠ 21 + tWB W + tWU W + (oB W).val →
      i.val ≠ 21 + 2 * tWB W + tWU W + (oU W).val →
      (i.val < 21 + 2 * tWB W + 2 * tWU W + tO ∨ 21 + 2 * tWB W + 2 * tWU W + 2 * tO ≤ i.val) → ι7.st i = ι6.st i :=
    fun i h1 h2 h3 => by rw [hι7, updS_st_other _ _ _ _ i (nO2 i h1 h2 h3)]; simp only [WState.seth_st]
  have sh7 : ∀ i, i ≠ sWT D → ι7.sh i = 0 := fun i hi => by
    rw [hι7, updS_sh_zero _ (mO2_inj hL)]; split_ifs
    · rfl
    · simp [WState.seth_sh, Function.update_of_ne hi, sh6 i hi]
  have sh7W : ι7.sh (sWT D) = pairEnd w := by
    rw [hι7, updS_sh_zero _ (mO2_inj hL), if_neg (fun ⟨j, hj⟩ => hWn _ _ g6 j hj), ← epe, hpe]; simp [countWord]; omega
  have hslot1 : mO1 D W RepairOrdinary.CloseoutWitness.Oracle.flagSlot = sF1 D W := hO1own _ (by decide) (by decide)
  have hslot2 : mO2 D W RepairOrdinary.CloseoutWitness.Oracle.flagSlot = sF2 D W := hO2own _ (by decide) (by decide)
  have hdsl1 : mO1 D W RepairOrdinary.CloseoutWitness.Oracle.descriptorSlot = sD1 D W :=
    hO1own _ (by decide) (by decide)
  have hdsl2 : mO2 D W RepairOrdinary.CloseoutWitness.Oracle.descriptorSlot = sD2 D W :=
    hO2own _ (by decide) (by decide)
  have vF1 := sF1_val hL
  have vF2 := sF2_val hL
  have vD1 := sD1_val hL
  have vD2 := sD2_val hL
  rw [hvq] at hfl5 hds5 hfl6 hds6
  set b1 := (decodeBooleanCircuit q (value f1)).isSome with hb1
  set b2 := (decodeBooleanCircuit q (value f2)).isSome with hb2
  have F1 : ι7.st (sF1 D W) = [b1] := by
    rw [st7 _ (by omega) (by omega) (by omega), hι6, ← hslot1, updS_st_slot _ _ _ _ (mO1_inj hL)]; exact hfl5
  have F2 : ι7.st (sF2 D W) = [b2] := by
    rw [hι7, ← hslot2, updS_st_slot _ _ _ _ (mO2_inj hL)]; exact hfl6
  have FL7 : ι7.st (sFL D) = [true] := by
    rw [st7 _ (by omega) (by omega) (by omega), st6 _ (by omega) (by omega) (by omega), st4 _ (by omega),
      st0 _ (fin_ne_of_val (by simp [sWT, fixS]; omega))]
    exact h0.fl
  -- 8. the flag
  have e8 := flagB_exec D W (cap := cap) ι7 b1 b2 F1 (sh7 _ (fin_ne_of_val (by simp [sWT, fixS]; omega))) F2
    (sh7 _ (fin_ne_of_val (by simp [sWT, fixS]; omega))) FL7 (sh7 _ (fin_ne_of_val (by simp [sWT, fixS]; omega)))
  set ι8 := ι7.sets (sFL D) [b1 && b2] with hι8
  set ιB := ι8.sets (sWT D) w with hιB
  -- the chain
  have E8 : ∃ τ, WXExec cap (flagB D W) ι7 τ 3 ∧ SimW ι8 τ := ⟨_, e8, SimW.refl _⟩
  obtain ⟨τA, eA, sA⟩ := Worker.seq_sim e1 s1 (Worker.seq_sim e2 s2 (Worker.seq_sim e3 s3 (Worker.seq_sim e4 s4
    (Worker.seq_sim (WXExec.wm e5) (SimW.refl _) (Worker.seq_sim e6 s6 (Worker.seq_sim e7 s7 E8))))))
  obtain ⟨τ, eB, sB⟩ := Worker.run_of_simW s0 eA
  have sBB : SimW ιB ι8 := CheckedPCPP.SimW.symm (Worker.simW_sets ι8 (sWT D) w (by
    rw [hι8, WState.sets_st, Function.update_of_ne (fin_ne_of_val (by simp [sWT, fixS]; omega)),
      st7 _ (by simp [sWT, fixS]; omega) (by simp [sWT, fixS]; omega) (by simp [sWT, fixS]; omega),
      st6 _ (by simp [sWT, fixS]; omega) (by simp [sWT, fixS]; omega) (by simp [sWT, fixS]; omega),
      st4 _ (by simp [sWT, fixS])]
    simp only [hι0', WState.sets_st, Function.update_self]
    exact guessWord_padB_rd N bits pad))
  refine ⟨τ, ιB, ?_, CheckedPCPP.SimW.trans sBB (CheckedPCPP.SimW.trans sA sB), ?_⟩
  · refine WXExec.mono eB ?_
    unfold costB fdCost
    rw [← ef1, ← ef2]
    simp only [List.length_ofFn]
    rw [← hqdef]
    omega
  · have hFLne : sFL D ≠ sWT D := fin_ne_of_val (by simp [sWT, fixS]; omega)
    have hB8 : ∀ i, i ≠ sWT D → ιB.st i = ι8.st i := fun i hi => by simp [hιB, Function.update_of_ne hi]
    have h87 : ∀ i, i ≠ sFL D → ι8.st i = ι7.st i := fun i hi => by simp [hι8, Function.update_of_ne hi]
    have far : ∀ i : Fin (nsW D + 1), i.val ≠ 2 → i.val ≠ 16 →
        (i.val < 21 ∨ 21 + 2 * tWB W + 2 * tWU W + 2 * tO ≤ i.val) → ιB.st i = ι0.st i := fun i h2 h16 hr => by
      have hW : i ≠ sWT D := fin_ne_of_val (by simpa [sWT, fixS] using h2)
      have hF : i ≠ sFL D := fin_ne_of_val (by omega)
      rw [hB8 i hW, h87 i hF, st7 i (by omega) (by omega) (by omega), st6 i (by omega) (by omega) (by omega),
        st4 i (by omega), st0 i hW]
    have v7 : ι7.val = fun r => if r = regE 6 then q else if r = rN then N else if r = rNu then nu N else 0 := by
      funext r
      show (ι4.setv (regE 6) q).val r = _
      simp only [WState.setv_val, Function.update_apply]
      have : ι4.val r = ι0.val r := rfl
      rw [this, h0.val]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [far _ (by simp [sX, fixS]) (by simp [sX, fixS]) (by simp [sX, fixS])]; exact h0.x
    · rw [far _ (by simp [sBW, fixS]) (by simp [sBW, fixS]) (by simp [sBW, fixS])]; exact h0.bw
    · rw [hιB, WState.sets_st, Function.update_self]
    · rw [hB8 _ hFLne]
      simp only [hι8, WState.sets_st, Function.update_self]
      unfold oracleOK
      rw [← hqdef, ← ef1, ← ef2]
    · intro c hc
      rw [← ef1] at hc
      rw [hB8 _ (fin_ne_of_val (by simp [sWT, fixS]; omega)), h87 _ (fin_ne_of_val (by omega)),
        st7 _ (by omega) (by omega) (by omega), hι6, ← hdsl1, updS_st_slot _ _ _ _ (mO1_inj hL)]
      exact hds5 c hc
    · intro c hc
      rw [← ef2] at hc
      rw [hB8 _ (fin_ne_of_val (by simp [sWT, fixS]; omega)), h87 _ (fin_ne_of_val (by omega)), hι7, ← hdsl2,
        updS_st_slot _ _ _ _ (mO2_inj hL)]
      exact hds6 c hc
    · intro i h0' h1 h2 h16 hr
      rw [far i h2 h16 hr]
      exact h0.blank i h0' h1 h2 h16
    · rw [hιB, WState.sets_sh, hι8, WState.sets_sh]
      funext i
      by_cases hi : i = sWT D
      · subst hi; rw [sh7W, if_pos rfl]
      · rw [sh7 i hi, if_neg hi]
    · rw [hιB, WState.sets_val, hι8, WState.sets_val]; exact v7
    · simp only [hιB, hι8, hι7, hι6, hι5, hι4, hι3, hι2, hι1, hι0', WState.sets_cell, WState.seth_cell,
        WState.setv_cell, updS_cell]
      exact h0.cell

end

end NearCubicGates.Close.Setup
