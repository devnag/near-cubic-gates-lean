import SourceAdapters.Refuter.RMachStep

/-!
# One round of R, end to end (input 7, R: the STEP machine against the protocol)

Paper anchor: proof of `lem:multitape-refuter` (one adaptive query per round; the output `x_p` at the end), proof of `cor:framed-refuter` (queries written in full on the query tape).

`stepP f = clrQO; arith; if FIN then outP else poseP f`. `Rep` is the word-level state between rounds
(protocol state `S`, the oracle's last answer `β`): the stored search state, the per-run constants, the
previous query on the compiler's output stream, every other scratch stream `[]`, heads and registers `0`.
`step_spec`: from `Rep S β`, one run of `stepP f` performs the protocol's `round`: it ends the search with
`x_p` on `OUT` and `DONE = 1`, or leaves the full query of the next state on the query tape, `DONE = 0`, and
— after the oracle writes any answer `β'` and the blank scratch streams are re-read as `[]` — `Rep S' β'`.
-/

namespace NearCubicGates.Adapters.Refuter.RM

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicGates.Adapters.Refuter NearCubicGates.Adapters.Compile
open NearCubicGates.Close.CheckedPCPP (clearPrefix runFrom_far)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {tT : ℕ} (cap : ℕ)
variable {budget : CNFCompilationRequest → ℕ} {query : CNFCompilationRequest → ℕ}
variable (f : WordFunction CNFCompilationRequest CNFCompilationRequest.word
  (fun r => RepairOrdinary.frame (query r).bits) budget)

local notation "WSf" => WState (NS f.program.tapeCount tT) NR

/-- **The round machine** (as a word program). -/
noncomputable def stepP : WMX (NS f.program.tapeCount tT) NR :=
  .seq (clrQO (qo (tT := tT) f)) (.seq arith (.ifs sFIN outP (poseP (tT := tT) f)))

/-- The word-level state between rounds. -/
structure Rep (code : List Bool) (mi xr g TN Lc : ℕ) (S : SS) (β : Bool) (σ : WSf) : Prop where
  srep : SRep (g + 2) σ S
  fuel : S.fuel ≤ g + 1
  code : σ.st sCODE = RepairOrdinary.frame code
  mu : σ.st sMU = List.replicate mi true
  xu : σ.st sXU = List.replicate xr true
  gu : σ.st sGU = List.replicate g true
  tu : σ.st sTU = List.replicate TN true
  z : σ.st sZ = num (g + 2) 0
  one : σ.st sONE = num (g + 2) 1
  sv : σ.st sSV = num (g + 2) (2 ^ g)
  ff : σ.st sFF = num (g + 2) (g + 1)
  q : ∃ v, σ.st sQ = num (g + 2) v
  tmp : ∃ v, σ.st sTMP = num (g + 2) v
  xh : ∃ v, σ.st sXH = num (g + 2) v
  ans : σ.st sANS = [β]
  done : σ.st sDONE = [false]
  fin : σ.st sFIN = [false]
  out : σ.st sOUT = []
  g0 : σ.st sG = []
  tl : σ.st sTL = []
  cs : ∀ j, j ≠ f.program.outputTape → σ.st (sC j) = []
  qo : ∃ l rest, σ.st (qo (tT := tT) f) = fpre l ++ rest ∧ (∀ q, readTapeBit rest q = false) ∧ l.length ≤ Lc
  log : σ.st sLOG = List.replicate Lc false
  sh : ∀ i, σ.sh i = 0
  val : ∀ r, σ.val r = 0
  cell : σ.cell = false

open Classical in
/-- After the oracle's answer `β'`: the answer cell, and the scratch streams that read blank re-read as `[]`. -/
noncomputable def reset (τ : WSf) (β' : Bool) : WSf :=
  ⟨τ.sh, fun i => if i = sANS then [β'] else
    if i = sG ∨ i = sTL ∨ (∃ j, j ≠ f.program.outputTape ∧ sC j = i) then [] else τ.st i, τ.val, τ.cell⟩

include f in
/-- The compiled query has at most `budget + 1` bits (it is written within the budget). -/
theorem bits_len_le (r : CNFCompilationRequest) : (query r).bits.length ≤ budget r + 1 := by
  obtain ⟨receipt, hrun, hout⟩ := f.realizes r
  have hf := runFrom_far f.program.machine f.program.outputTape (budget r) _ 0 receipt hrun
    (by simp [initialConfiguration])
    (fun q _ => by
      simp only [initialConfiguration, Program.inputTapes]
      rw [if_neg f.program.outputFresh]; rfl)
  have hsteps : receipt.steps ≤ budget r := runFrom_steps_le _ _ _ receipt hrun
  by_contra hc
  have hk : 0 < (query r).bits.length := by omega
  have hm := (rd_fpre (query r).bits [false] ((query r).bits.length - 1) (by omega)).1
  rw [← frame_eq_fpre] at hm
  have hout' : receipt.final.tapes f.program.outputTape = RepairOrdinary.frame (query r).bits := hout
  rw [← hout', hf.2 _ (by omega)] at hm
  exact Bool.false_ne_true hm

/-- What one round leaves. -/
def StepW (M : OrdinaryWeakMachine) (T : ℕ → ℕ) (N : ℕ) (code : List Bool) (mi xr g TN Lc : ℕ) (τ : WSf) :
    SS ⊕ ℕ → Prop
  | .inr p => τ.st sDONE = [true] ∧ τ.st sOUT = RepairOrdinary.frame (List.ofFn (record M N p)) ∧
      (∀ i, τ.sh i = 0) ∧ (∀ r, τ.val r = 0) ∧ τ.cell = false
  | .inl S' => τ.st sDONE = [false] ∧
      (∃ pad, τ.st (qo (tT := tT) f) = RepairOrdinary.frame (query (stateRequest M T N S')).bits ++ pad) ∧
      (∀ i, τ.sh i = 0) ∧ (∀ r, τ.val r = 0) ∧ τ.cell = false ∧ (∃ b, τ.st sANS = [b]) ∧
      (∀ q, readTapeBit (τ.st sG) q = false) ∧ (∀ q, readTapeBit (τ.st sTL) q = false) ∧
      (∀ j, j ≠ f.program.outputTape → ∀ q, readTapeBit (τ.st (sC j)) q = false) ∧
      (∀ β', Rep f code mi xr g TN Lc S' β' (reset f τ β'))

theorem range_next (g : ℕ) (S : SS) (β : Bool) (hG : Good (2 ^ g) S) (S' : SS)
    (h : round (2 ^ g) (g + 1) S β = .inl S') : Range (2 ^ g) S' := by
  rcases hG with rfl | ⟨hP, hR⟩
  · rw [fresh_round] at h; cases h
    exact ⟨le_rfl, Nat.zero_le _, fun h => by simp [SS.first] at h⟩
  · exact (round_range _ _ Nat.one_le_two_pow S hP hR β S' h).2

/-- **One round.** -/
theorem step_spec (M : OrdinaryWeakMachine) (T : ℕ → ℕ) (N : ℕ) (code : List Bool) (mi xr g TN Lc : ℕ)
    (hcode : code = VerifierEncoding.code M.verifier) (hmi : mi = machineIndex M) (hgN : g = N / 16)
    (hxr : xr = N - N / 16 - machineIndex M - 2) (hTN : TN = T N) (hg1 : 1 ≤ g)
    (hrec : machineIndex M + 2 + N / 16 ≤ N)
    (hLc : ∀ S', Range (2 ^ g) S' → budget (stateRequest M T N S') + 1 ≤ Lc)
    (hcap : 40 * (code.length + mi + xr + g + TN + Lc + 10) ≤ cap)
    (S : SS) (β : Bool) (σ : WSf) (hR : Rep f code mi xr g TN Lc S β σ) (hG : Good (2 ^ g) S) :
    ∃ τ, WXExec cap (stepP (tT := tT) f) σ τ
        ((f.program.tapeCount + 3) * 2000 * (code.length + mi + xr + g + TN + Lc + 10) ^ 2) ∧
      StepW f M T N code mi xr g TN Lc τ (round (2 ^ g) (g + 1) S β) := by
  set L := code.length + mi + xr + g + TN with hL
  obtain ⟨hp1, hp2, hp3⟩ := pow_facts g
  -- erase the previous query
  obtain ⟨l, rest, hQO, hrest, hl⟩ := hR.qo
  have e1 := clrQO_spec cap (qo (tT := tT) f) σ l rest hQO hrest (hR.sh _) (hR.val _) (by omega)
  set σ1 := σ.sets (qo (tT := tT) f) (clearPrefix (2 * l.length) (fpre l ++ rest)) with hσ1
  have hqoF : ∀ X : Fin (NS f.program.tapeCount tT + 1), X.val < 41 → X ≠ qo (tT := tT) f := fun X h =>
    sC_ne _ _ h
  have h1st : ∀ X, X ≠ qo (tT := tT) f → σ1.st X = σ.st X := fun X h => by
    simp [σ1, Function.update_of_ne h]
  have hS1 : SRep (g + 2) σ1 S :=
    ⟨by rw [h1st _ (hqoF _ (by simp)), hR.srep.lo], by rw [h1st _ (hqoF _ (by simp)), hR.srep.hi],
      by rw [h1st _ (hqoF _ (by simp)), hR.srep.fu], by rw [h1st _ (hqoF _ (by simp)), hR.srep.p0],
      by rw [h1st _ (hqoF _ (by simp)), hR.srep.p1], by rw [h1st _ (hqoF _ (by simp)), hR.srep.p3],
      by rw [h1st _ (hqoF _ (by simp)), hR.srep.elo]⟩
  obtain ⟨vq, hvq⟩ := hR.q
  obtain ⟨vt, hvt⟩ := hR.tmp
  have e2 := arith_spec (cap := cap) g hg1 (by omega) σ1 S β vq vt hS1 hR.fuel hG
    (by rw [h1st _ (hqoF _ (by simp)), hR.z]) (by rw [h1st _ (hqoF _ (by simp)), hR.one])
    (by rw [h1st _ (hqoF _ (by simp)), hR.sv]) (by rw [h1st _ (hqoF _ (by simp)), hR.ff])
    (by rw [h1st _ (hqoF _ (by simp)), hR.ans]) (by rw [h1st _ (hqoF _ (by simp)), hR.fin])
    (by rw [h1st _ (hqoF _ (by simp)), hvq]) (by rw [h1st _ (hqoF _ (by simp)), hvt]) (fun i => by simp [σ1, hR.sh])
    (by simp [σ1, hR.val]) (by simp [σ1, hR.val]) (by simp [σ1, hR.val]) (by simp [σ1, hR.val])
  obtain ⟨τa, e2, hfa, ⟨vq', hvq'⟩, ⟨vt', hvt'⟩, hout⟩ := e2
  -- facts about `τa` outside the arithmetic's streams
  have hAL : ∀ X : Fin (NS f.program.tapeCount tT + 1), X ∉ AL → τa.st X = σ1.st X := hfa.1
  have hash : ∀ i, τa.sh i = 0 := fun i => by rw [hfa.2.1]; simp [σ1, hR.sh]
  have haval : ∀ r, τa.val r = 0 := fun r => by rw [hfa.2.2.1]; simp [σ1, hR.val]
  have hacell : τa.cell = false := by rw [hfa.2.2.2]; simp [σ1, hR.cell]
  have hnAL : ∀ X : Fin (NS f.program.tapeCount tT + 1), X ∈ [sCODE, sMU, sXU, sGU, sTU, sZ, sONE, sSV, sFF, sANS,
      sDONE, sOUT, sG, sTL, sLOG, sXH] → X ∉ AL := by
    intro X hX; simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp [AL, Fin.ext_iff]
  have hCAL : ∀ j : Fin f.program.tapeCount, (sC (tT := tT) j) ∉ (AL : List (Fin (NS f.program.tapeCount tT + 1))) := fun j => by
    simp only [AL, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact (sC_ne _ _ (by simp)).symm
  have hast : ∀ X : Fin (NS f.program.tapeCount tT + 1), X ∈ [sCODE, sMU, sXU, sGU, sTU, sZ, sONE, sSV, sFF, sANS,
      sDONE, sOUT, sG, sTL, sLOG, sXH] → τa.st X = σ.st X := fun X hX => by
    rw [hAL X (hnAL X hX), h1st X (hqoF X (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp))]
  -- the two kinds of outcome
  cases hr : round (2 ^ g) (g + 1) S β with
  | inr p =>
    rw [hr] at hout
    obtain ⟨hLOp, hFIN⟩ := hout
    have e3 := out_spec cap τa mi xr g p (by rw [hast _ (by simp), hR.out]) (by rw [hast _ (by simp), hR.mu])
      (by rw [hast _ (by simp), hR.xu]) hLOp (by rw [hast _ (by simp), hR.done]) hash (haval _) (haval _) (by omega)
    refine ⟨_, (WXExec.seq e1 (WXExec.seq e2 (WXExec.ifsT (by simp [wbit, hFIN, hash, readTapeBit]) e3))).mono ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · have hlL : l.length ≤ L + Lc + 10 := by omega
      have hgL : mi + xr + g + 5 ≤ L + Lc + 10 := by omega
      have hX : 10 ≤ L + Lc + 10 := by omega
      have hT : 3 ≤ f.program.tapeCount + 3 := by omega
      generalize f.program.tapeCount + 3 = T3 at hT ⊢
      generalize L + Lc + 10 = X at hlL hgL hX ⊢
      clear * - hlL hgL hX hT
      have a1 : 800 * X ≤ 80 * (X * X) := by nlinarith
      have a2 : 80 * (X * X) ≤ T3 * 2000 * (X * X) := by nlinarith
      rw [sq]
      omega
    · simp [Function.update_apply, Fin.ext_iff]
    · simp only [WState.sets_st, Function.update_of_ne (show (sOUT : Fin (NS f.program.tapeCount tT + 1)) ≠ sDONE by ds),
        Function.update_self]
      rw [record_list M N p hrec, hmi, hgN, hxr]
    · intro i; simp [hash]
    · intro r; simp [haval]
    · simp [hacell]
  | inl S' =>
    rw [hr] at hout
    obtain ⟨hS', hFIN, hfuel'⟩ := hout
    have hRg := range_next g S β hG S' hr
    have hlh : S'.lo + S'.hi < 2 ^ (g + 2) := by have := hRg.1; have := hRg.2.1; omega
    set req := stateRequest M T N S' with hreq
    have hw : req.word = if decide (S'.ph = 3) then intWord code mi xr g TN ((S'.lo + S'.hi) / 2) else
        memWord code mi xr g TN ((S'.lo + S'.hi) / 2) := by
      simp only [req, stateRequest]
      by_cases h3 : S'.ph = 3
      · simp only [h3, if_true, decide_true]
        rw [intervalRequest_word M T N _ hrec, hcode, hmi, hxr, hgN, hTN]; rfl
      · simp only [h3, if_false, decide_false]
        rw [memberRequest_word M T N _ hrec, hcode, hmi, hxr, hgN, hTN]; rfl
    have hs : ReqSrc τa code mi xr g TN :=
      ⟨by rw [hast _ (by simp), hR.code], by rw [hast _ (by simp), hR.mu], by rw [hast _ (by simp), hR.xu],
        by rw [hast _ (by simp), hR.gu], by rw [hast _ (by simp), hR.tu], by rw [hast _ (by simp), hR.z], hash,
        haval _, haval _, haval _, haval _, haval _⟩
    obtain ⟨vx, hvx⟩ := hR.xh
    have e3 := pose_spec cap f τa code mi xr g TN S'.lo S'.hi Lc (decide (S'.ph = 3)) req hs hS'.lo hS'.hi hlh
      ⟨vq', hvq'⟩ ⟨vx, by rw [hast _ (by simp), hvx]⟩ hS'.p3 hw
      (fun j hj => by
        rw [hAL _ (hCAL j), h1st _ (fun h => hj (sC_inj h))]; exact hR.cs j hj)
      (by
        intro q
        rw [show qo (tT := tT) f = sC f.program.outputTape from rfl, hAL _ (hCAL _)]
        simp only [σ1, qo, WState.sets_st, Function.update_self]
        exact clearPrefix_fpre_blank l rest hrest q)
      (by rw [hast _ (by simp), hR.tl]) (by rw [hast _ (by simp), hR.g0]) (by rw [hast _ (by simp), hR.log])
      (hLc S' hRg) haval (by omega)
    obtain ⟨τ, e3, ⟨z, hqz⟩, hcs', htl', hg', hQ', ⟨vx', hvx'⟩, hoth, hsh', hval', hcell'⟩ := e3
    have hoth' : ∀ X : Fin (NS f.program.tapeCount tT + 1), X.val < 41 → X ≠ sTL → X ≠ sG → X ≠ sQ → X ≠ sXH →
        τ.st X = τa.st X := fun X hX h1 h2 h3 h4 => hoth X (fun j hj => by
          have := congrArg Fin.val hj; simp at this; omega) h1 h2 h3 h4
    refine ⟨τ, (WXExec.seq e1 (WXExec.seq e2 (WXExec.ifsF (by simp [wbit, hFIN, hash, readTapeBit]) e3))).mono ?_,
      ?_, ⟨List.replicate (z - (RepairOrdinary.frame (query req).bits).length) false, by rw [hqz]; rfl⟩, hsh', hval',
      ?_, ⟨β, ?_⟩, hg', htl', hcs', fun β' => ?_⟩
    · have hlL : l.length ≤ L + Lc + 10 := by omega
      have hgL : g + 2 ≤ L + Lc + 10 := by omega
      have hX : 10 ≤ L + Lc + 10 := by omega
      have hT : 3 ≤ f.program.tapeCount + 3 := by omega
      generalize f.program.tapeCount + 3 = T3 at hT ⊢
      generalize L + Lc + 10 = X at hlL hgL hX ⊢
      clear * - hlL hgL hX hT
      have a1 : 800 * X ≤ 80 * (X * X) := by nlinarith
      have a2 : 80 * (X * X) + T3 * 1000 * (X * X) ≤ T3 * 2000 * (X * X) := by nlinarith
      rw [sq]
      omega
    · rw [hoth' _ (by simp) (by ds) (by ds) (by ds) (by ds), hast _ (by simp), hR.done]
    · rw [hcell', hacell]
    · rw [hoth' _ (by simp) (by ds) (by ds) (by ds) (by ds), hast _ (by simp), hR.ans]
    · have hrs : ∀ X : Fin (NS f.program.tapeCount tT + 1), X ≠ sANS → X ≠ sG → X ≠ sTL →
          (∀ j, sC j ≠ X) → (reset f τ β').st X = τ.st X := by
        intro X h1 h2 h3 h4
        simp only [reset, h1, h2, h3, if_false, false_or]
        rw [if_neg]; rintro ⟨j, -, hj⟩; exact h4 j hj
      have hfix : ∀ X : Fin (NS f.program.tapeCount tT + 1), X.val < 41 → (∀ j, sC (tT := tT) j ≠ X) := fun X hX j hj => by
        have := congrArg Fin.val hj; simp at this; omega
      -- streams outside the query step's reach: as after `arith`
      have hA : ∀ X : Fin (NS f.program.tapeCount tT + 1), X.val < 41 → X ≠ sANS → X ≠ sG → X ≠ sTL → X ≠ sQ →
          X ≠ sXH → (reset f τ β').st X = τa.st X := fun X hX h1 h2 h3 h4 h5 => by
        rw [hrs X h1 h2 h3 (hfix X hX), hoth' X hX h3 h2 h4 h5]
      have hB : ∀ X : Fin (NS f.program.tapeCount tT + 1), X ∈ [sCODE, sMU, sXU, sGU, sTU, sZ, sONE, sSV, sFF, sANS,
          sDONE, sOUT, sG, sTL, sLOG, sXH] → X.val < 41 → X ≠ sANS → X ≠ sG → X ≠ sTL → X ≠ sQ → X ≠ sXH →
          (reset f τ β').st X = σ.st X := fun X hX h0 h1 h2 h3 h4 h5 => by
        rw [hA X h0 h1 h2 h3 h4 h5, hast X hX]
      have hbits := bits_len_le f req
      have hLcS : budget req + 1 ≤ Lc := hLc S' hRg
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hfuel', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨(S'.lo + S'.hi) / 2, ?_⟩,
        ⟨vt', ?_⟩, ⟨vx', ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i => ?_, fun r => ?_, ?_⟩
      · rw [hA _ (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)]; exact hS'.lo
      · rw [hA _ (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)]; exact hS'.hi
      · rw [hA _ (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)]; exact hS'.fu
      · rw [hA _ (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)]; exact hS'.p0
      · rw [hA _ (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)]; exact hS'.p1
      · rw [hA _ (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)]; exact hS'.p3
      · rw [hA _ (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)]; exact hS'.elo
      · rw [hB _ (by simp) (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)]; exact hR.code
      · rw [hB _ (by simp) (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)]; exact hR.mu
      · rw [hB _ (by simp) (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)]; exact hR.xu
      · rw [hB _ (by simp) (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)]; exact hR.gu
      · rw [hB _ (by simp) (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)]; exact hR.tu
      · rw [hB _ (by simp) (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)]; exact hR.z
      · rw [hB _ (by simp) (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)]; exact hR.one
      · rw [hB _ (by simp) (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)]; exact hR.sv
      · rw [hB _ (by simp) (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)]; exact hR.ff
      · rw [hrs _ (by ds) (by ds) (by ds) (hfix _ (by simp))]; exact hQ'
      · rw [hA _ (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)]; exact hvt'
      · rw [hrs _ (by ds) (by ds) (by ds) (hfix _ (by simp))]; exact hvx'
      · simp [reset]
      · rw [hB _ (by simp) (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)]; exact hR.done
      · rw [hA _ (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)]; exact hFIN
      · rw [hB _ (by simp) (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)]; exact hR.out
      · simp [reset, show (sG : Fin (NS f.program.tapeCount tT + 1)) ≠ sANS by ds]
      · simp [reset, show (sTL : Fin (NS f.program.tapeCount tT + 1)) ≠ sANS by ds]
      · intro j hj
        have : sC (tT := tT) j ≠ sANS := sC_ne _ _ (by simp) |>.symm
        simp only [reset, this, if_false]
        rw [if_pos (Or.inr (Or.inr ⟨j, hj, rfl⟩))]
      · refine ⟨(query req).bits, false :: List.replicate (z - (RepairOrdinary.frame (query req).bits).length) false,
          ?_, ?_, by omega⟩
        · have hne1 : (qo (tT := tT) f) ≠ sANS := (sC_ne _ _ (by simp)).symm
          have hne2 : (qo (tT := tT) f) ≠ sG := (sC_ne _ _ (by simp)).symm
          have hne3 : (qo (tT := tT) f) ≠ sTL := (sC_ne _ _ (by simp)).symm
          have hne4 : ¬ ∃ j, j ≠ f.program.outputTape ∧ sC (tT := tT) j = qo (tT := tT) f := by
            rintro ⟨j, hj, e⟩; exact hj (sC_inj e)
          simp only [reset, hne1, hne2, hne3, hne4, if_false, or_false, false_or]
          rw [hqz, ZeroPadding.pad, frame_eq_fpre, List.append_assoc]; rfl
        · intro q; cases q with
          | zero => rfl
          | succ q => exact blank_replicate _ q
      · rw [hB _ (by simp) (by simp) (by ds) (by ds) (by ds) (by ds) (by ds)]; exact hR.log
      · exact hsh' i
      · exact hval' r
      · simp only [reset]; rw [hcell', hacell]

end NearCubicGates.Adapters.Refuter.RM
