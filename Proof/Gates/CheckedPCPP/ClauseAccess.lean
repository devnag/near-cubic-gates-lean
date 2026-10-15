import Proof.Gates.CheckedPCPP.WMXReady
import Proof.MachineModel.FrameSkip
import Proof.MachineModel.FrameCopy
import Proof.Gates.PublishedSources.PCPP

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CheckedPCPP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicGates.Close.WordPrograms

namespace ClauseAccess

/-- Streams: the word, the unary clause index, the two header fields, the three literal codes, five scratch
counters. -/
abbrev J : Fin 12 := 0
abbrev C : Fin 12 := 1
abbrev PB : Fin 12 := 2
abbrev RB : Fin 12 := 3
abbrev L0 : Fin 12 := 4
abbrev L1 : Fin 12 := 5
abbrev L2 : Fin 12 := 6
abbrev A0 : Fin 12 := 7
abbrev A1 : Fin 12 := 8
abbrev A2 : Fin 12 := 9
abbrev A3 : Fin 12 := 10
abbrev A4 : Fin 12 := 11

/-- Skip one framed field of `J`. -/
def skip : WMX 11 0 := .mach FrameSkip.machine ![J]
/-- Copy one framed field of `J` onto `D`, with scratch `A`. -/
def copy (D A : Fin 12) : WMX 11 0 := .mach FrameCopy.machine ![J, D, A]

variable {cap : ℕ}

theorem skip_exec (σ : WState 11 0) (pre w rest : List Bool) (hst : σ.st J = pre ++ frame w ++ rest)
    (hsh : σ.sh J = pre.length) :
    WXExec cap skip σ (σ.seth J (pre.length + (frame w).length)) (2 * w.length + 1) := by
  obtain ⟨r, hr, hf, _⟩ := FrameSkip.skip_run pre w rest
  have hstart : (⟨FrameSkip.machine.start, fun j => σ.sh (![J] j), fun j => σ.st (![J] j)⟩ :
      Configuration 1 3) = FrameSkip.cfg 0 (pre ++ frame w ++ rest) pre.length := by
    apply configuration_ext
    · rfl
    · funext j; fin_cases j; exact hsh
    · funext j; fin_cases j; exact hst
  rw [← hstart] at hr
  refine WXExec.mach_of cap (by intro a b _; exact Subsingleton.elim a b) (Step.of_run hr rfl rfl) ?_ ?_ ?_ rfl rfl
  · intro j; fin_cases j; rw [hf]; simp [FrameSkip.cfg, hst]
  · intro j; fin_cases j; rw [hf]; simp [FrameSkip.cfg]
  · intro i hi
    have hne : i ≠ J := fun h => hi 0 (by simp [h])
    simp [WState.seth, Function.update, hne]

theorem copy_exec (D A : Fin 12) (hJD : J ≠ D) (hJA : J ≠ A) (hDA : D ≠ A) (σ : WState 11 0)
    (pre w rest : List Bool) (hst : σ.st J = pre ++ frame w ++ rest) (hsh : σ.sh J = pre.length)
    (hD : σ.st D = []) (hDh : σ.sh D = 0) (hA : σ.st A = []) (hAh : σ.sh A = 0) :
    WXExec cap (copy D A) σ
      (((σ.seth J (pre.length + (frame w).length)).sets D (frame w)).sets A
        (List.replicate (frame w).length false)) (2 * (frame w).length + 2) := by
  obtain ⟨r, hr, hf, _⟩ := FrameCopy.copy_run pre w rest
  have hinj : Function.Injective (![J, D, A] : Fin 3 → Fin 12) := by
    have h1 := hJD.symm
    have h2 := hJA.symm
    have h3 := hDA.symm
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all
  have hstart : (⟨FrameCopy.machine.start, fun j => σ.sh (![J, D, A] j), fun j => σ.st (![J, D, A] j)⟩ :
      Configuration 3 5) = FrameCopy.cfg 0 (pre ++ frame w ++ rest) pre.length [] 0 [] 0 := by
    apply configuration_ext
    · rfl
    · funext j; fin_cases j <;> simp [FrameCopy.cfg, hsh, hDh, hAh]
    · funext j; fin_cases j <;> simp [FrameCopy.cfg, hst, hD, hA]
  rw [← hstart] at hr
  refine WXExec.mach_of cap hinj (Step.of_run hr rfl rfl) ?_ ?_ ?_ rfl rfl
  · intro j; fin_cases j <;> rw [hf] <;> simp [FrameCopy.cfg, WState.sets, WState.seth, Function.update, hst,
      hJD, hJA, hDA, hJD.symm, hJA.symm, hDA.symm]
  · intro j; fin_cases j <;> rw [hf] <;> simp [FrameCopy.cfg, WState.sets, WState.seth, Function.update,
      hJD, hJA, hDA, hJD.symm, hJA.symm, hDA.symm, hDh, hAh]
  · intro i hi
    have h0 : i ≠ J := fun h => hi 0 (by simp [h])
    have h1 : i ≠ D := fun h => hi 1 (by simp [h])
    have h2 : i ≠ A := fun h => hi 2 (by simp [h])
    simp [WState.sets, WState.seth, Function.update, h0, h1, h2]

/-- Three framed fields. -/
def tri (t : List Bool × List Bool × List Bool) : List Bool := frame t.1 ++ frame t.2.1 ++ frame t.2.2

/-- Skip three fields, advance the clause counter. -/
def body : WMX 11 0 := .seq skip (.seq skip (.seq skip (WMX.fwd C)))

theorem seth_seth (σ : WState 11 0) (i : Fin 12) (a b : ℕ) : (σ.seth i a).seth i b = σ.seth i b :=
  WState.eq (by funext j; simp [Function.update]; split_ifs <;> rfl) rfl rfl rfl

theorem body_exec (σ : WState 11 0) (pre rest : List Bool) (t : List Bool × List Bool × List Bool)
    (hst : σ.st J = pre ++ tri t ++ rest) (hsh : σ.sh J = pre.length) :
    WXExec cap body σ ((σ.seth J (pre.length + (tri t).length)).seth C (σ.sh C + 1)) ((tri t).length + 4) := by
  obtain ⟨w0, w1, w2⟩ := t
  have e1 : σ.st J = pre ++ frame w0 ++ (frame w1 ++ frame w2 ++ rest) := by
    rw [hst]; simp [tri, List.append_assoc]
  have s1 := skip_exec (cap := cap) σ pre w0 _ e1 hsh
  let σ1 := σ.seth J (pre.length + (frame w0).length)
  have e2 : σ1.st J = (pre ++ frame w0) ++ frame w1 ++ (frame w2 ++ rest) := by
    simp only [σ1, WState.seth_st, hst]; simp [tri, List.append_assoc]
  have s2 := skip_exec (cap := cap) σ1 (pre ++ frame w0) w1 _ e2 (by simp [σ1])
  let σ2 := σ1.seth J ((pre ++ frame w0).length + (frame w1).length)
  have e3 : σ2.st J = (pre ++ frame w0 ++ frame w1) ++ frame w2 ++ rest := by
    simp only [σ2, σ1, WState.seth_st, hst]; simp [tri, List.append_assoc]
  have s3 := skip_exec (cap := cap) σ2 (pre ++ frame w0 ++ frame w1) w2 rest e3 (by simp [σ2, σ1]; omega)
  let σ3 := σ2.seth J ((pre ++ frame w0 ++ frame w1).length + (frame w2).length)
  have s4 := WXExec.fwd (cap := cap) C σ3
  have h := WXExec.seq s1 (WXExec.seq s2 (WXExec.seq s3 s4))
  refine WXExec.mono (WXExec.cast cap h ?_ le_rfl) ?_
  · simp only [σ3, σ2, σ1, seth_seth]
    apply WState.eq
    · funext j; simp [Function.update, tri]; split_ifs <;> omega
    · rfl
    · rfl
    · rfl
  · simp [tri]; omega

/-- The clause loop. -/
def loop : WMX 11 0 := .whs C body

theorem readTapeBit_replicate (c i : ℕ) : readTapeBit (List.replicate c true) i = decide (i < c) := by
  unfold readTapeBit
  by_cases h : i < c
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp [h]
  · rw [List.getD_eq_default _ _ (by simpa using h)]
    simp [h]

theorem flatten_split (ts : List (List Bool × List Bool × List Bool)) (i : ℕ) (hi : i < ts.length) :
    (ts.map tri).flatten = ((ts.take i).map tri).flatten ++ tri ts[i] ++ ((ts.drop (i+1)).map tri).flatten := by
  nth_rewrite 1 [← List.take_append_drop i ts]
  rw [List.drop_eq_getElem_cons hi, List.map_append, List.flatten_append, List.map_cons, List.flatten_cons]
  simp only [List.append_assoc]

theorem take_succ_tri (ts : List (List Bool × List Bool × List Bool)) (i : ℕ) (hi : i < ts.length) :
    ((ts.take (i+1)).map tri).flatten = ((ts.take i).map tri).flatten ++ tri ts[i] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.flatten_append,
    List.flatten_cons, List.flatten_nil, List.append_nil]

theorem loop_exec (head rest : List Bool) (ts : List (List Bool × List Bool × List Bool)) (c T : ℕ)
    (hc : c ≤ ts.length) (hT : ∀ t ∈ ts, (tri t).length ≤ T) :
    ∀ k i, i + k = c → ∀ σ : WState 11 0, σ.st J = head ++ (ts.map tri).flatten ++ rest →
      σ.sh J = head.length + ((ts.take i).map tri).flatten.length → σ.st C = List.replicate c true →
      σ.sh C = i →
      WXExec cap loop σ ((σ.seth J (head.length + ((ts.take c).map tri).flatten.length)).seth C c)
        (k * (T + 6) + 1)
  | 0, i, hik, σ, _, hJ, hC, hCh => by
    have hi : i = c := by omega
    subst hi
    have hb : wbit σ C = false := by
      simp [wbit, hC, hCh, readTapeBit_replicate]
    have e : (σ.seth J (head.length + ((ts.take i).map tri).flatten.length)).seth C i = σ := by
      apply WState.eq
      · funext j; simp [Function.update]; split_ifs with h1 h2 <;> subst_vars <;> simp_all
      · rfl
      · rfl
      · rfl
    rw [e]
    exact WXExec.mono (WXExec.whsF hb) (by omega)
  | k+1, i, hik, σ, hst, hJ, hC, hCh => by
    have hi : i < ts.length := by omega
    have hb : wbit σ C = true := by
      simp only [wbit, hC, hCh, readTapeBit_replicate, decide_eq_true_eq]; omega
    have hsplit : σ.st J = (head ++ ((ts.take i).map tri).flatten) ++ tri ts[i] ++
        (((ts.drop (i+1)).map tri).flatten ++ rest) := by
      rw [hst, flatten_split ts i hi]; simp [List.append_assoc]
    have hb1 := body_exec (cap := cap) σ _ _ ts[i] hsplit (by rw [hJ]; simp)
    let σ' := (σ.seth J ((head ++ ((ts.take i).map tri).flatten).length + (tri ts[i]).length)).seth C (σ.sh C + 1)
    have ih := loop_exec head rest ts c T hc hT k (i+1) (by omega) σ' (by simp [σ', hst])
      (by
        have e : σ'.sh J = (head ++ ((ts.take i).map tri).flatten).length + (tri ts[i]).length := by
          simp only [σ', WState.seth_sh, Function.update_apply, if_neg (show (J : Fin 12) ≠ C by decide), if_true]
        rw [e, take_succ_tri ts i hi]
        simp only [List.length_append]
        omega) (by simp [σ', hC]) (by simp [σ', hCh])
    have hle : (tri ts[i]).length ≤ T := hT _ (List.getElem_mem hi)
    refine WXExec.mono (WXExec.cast cap (WXExec.whsT hb hb1 ih) ?_ le_rfl) ?_
    · apply WState.eq
      · funext j; simp [σ', Function.update]; split_ifs <;> rfl
      · rfl
      · rfl
      · rfl
    · nlinarith

/-- **The clause-access program.** -/
def program : WMX 11 0 :=
  .seq (copy PB A0) (.seq (copy RB A1) (.seq loop (.seq (copy L0 A2) (.seq (copy L1 A3) (copy L2 A4)))))

/-- The start state: the word on `J`, `c` in unary on `C`, every other stream empty, all heads at `0`. -/
def start (word : List Bool) (c : ℕ) : WState 11 0 :=
  ⟨fun _ => 0, fun i => if i = J then word else if i = C then List.replicate c true else [], Fin.elim0, false⟩

/-- The step bound, in the word length and the clause index. -/
def cost (W c : ℕ) : ℕ := (c + 11) * (W + 6)

open NearCubicGates.PublishedSources.PCPP in
/-- The literal-code triples of the clauses. -/
def triples {n : ℕ} (raw : RawThreeQueryPCPP n) : List (List Bool × List Bool × List Bool) :=
  List.ofFn fun j : Fin (2 ^ raw.randomBits) => ((RepairSource.literalCode (raw.clause j 0)).bits,
    (RepairSource.literalCode (raw.clause j 1)).bits, (RepairSource.literalCode (raw.clause j 2)).bits)

open NearCubicGates.PublishedSources.PCPP in
theorem clauses_eq {n : ℕ} (raw : RawThreeQueryPCPP n) :
    (List.ofFn fun coins : Fin (2 ^ raw.randomBits) => (List.ofFn fun i : Fin 3 =>
      frame (RepairSource.literalCode (raw.clause coins i)).bits).flatten) = (triples raw).map tri := by
  simp only [triples, List.map_ofFn]
  congr 1
  funext j
  simp [tri, List.ofFn_succ, List.append_assoc]

open NearCubicGates.PublishedSources.PCPP in
theorem word_eq {n : ℕ} (raw : RawThreeQueryPCPP n) :
    raw.word = (frame raw.proofBits.bits ++ frame raw.randomBits.bits) ++ ((triples raw).map tri).flatten := by
  rw [RawThreeQueryPCPP.word, clauses_eq]

open NearCubicGates.PublishedSources.PCPP in

theorem program_exec {n : ℕ} (raw : RawThreeQueryPCPP n) (c : Fin (2 ^ raw.randomBits)) :
    ∃ τ : WState 11 0, WXExec cap program (start raw.word c) τ (cost raw.word.length c) ∧
      τ.st PB = frame raw.proofBits.bits ∧ τ.st RB = frame raw.randomBits.bits ∧
      τ.st L0 = frame (RepairSource.literalCode (raw.clause c 0)).bits ∧ τ.st L1 = frame (RepairSource.literalCode (raw.clause c 1)).bits ∧
      τ.st L2 = frame (RepairSource.literalCode (raw.clause c 2)).bits := by
  have hw := word_eq raw
  set W := raw.word.length
  set ts := triples raw
  have hlen : ts.length = 2 ^ raw.randomBits := by simp [ts, triples]
  have hc : c.val < ts.length := by rw [hlen]; exact c.isLt
  set head := frame raw.proofBits.bits ++ frame raw.randomBits.bits
  have hT : ∀ t ∈ ts, (tri t).length ≤ W := by
    intro t ht
    have := (List.sublist_flatten_of_mem (List.mem_map_of_mem (f := tri) ht)).length_le
    simp only [W, hw, List.length_append]
    omega
  set σ0 := start raw.word c
  -- the two header copies
  have h1 := copy_exec (cap := cap) PB A0 (by decide) (by decide) (by decide) σ0 [] raw.proofBits.bits
    (frame raw.randomBits.bits ++ (ts.map tri).flatten)
    (by simp (config := { decide := true }) [σ0, start, hw, head, ts, List.append_assoc, Function.update]) (by simp (config := { decide := true }) [σ0, start, Function.update]) (by simp (config := { decide := true }) [σ0, start, Function.update])
    (by simp (config := { decide := true }) [σ0, start, Function.update]) (by simp (config := { decide := true }) [σ0, start, Function.update]) (by simp (config := { decide := true }) [σ0, start, Function.update])
  set σ1 := ((σ0.seth J ([].length + (frame raw.proofBits.bits).length)).sets PB (frame raw.proofBits.bits)).sets A0
    (List.replicate (frame raw.proofBits.bits).length false)
  have h2 := copy_exec (cap := cap) RB A1 (by decide) (by decide) (by decide) σ1 (frame raw.proofBits.bits)
    raw.randomBits.bits ((ts.map tri).flatten)
    (by simp (config := { decide := true }) [σ1, σ0, start, hw, head, ts, List.append_assoc, Function.update]) (by simp (config := { decide := true }) [σ1, σ0, start, Function.update])
    (by simp (config := { decide := true }) [σ1, σ0, start, Function.update]) (by simp (config := { decide := true }) [σ1, σ0, start, Function.update]) (by simp (config := { decide := true }) [σ1, σ0, start, Function.update]) (by simp (config := { decide := true }) [σ1, σ0, start, Function.update])
  set σ2 := ((σ1.seth J ((frame raw.proofBits.bits).length + (frame raw.randomBits.bits).length)).sets RB
    (frame raw.randomBits.bits)).sets A1 (List.replicate (frame raw.randomBits.bits).length false)
  -- the loop
  have h3 := loop_exec (cap := cap) head [] ts c.val W hc.le hT c.val 0 (by omega) σ2
    (by simp (config := { decide := true }) [σ2, σ1, σ0, start, hw, head, ts, Function.update]) (by simp (config := { decide := true }) [σ2, σ1, σ0, start, head, Function.update])
    (by simp (config := { decide := true }) [σ2, σ1, σ0, start, Function.update]) (by simp (config := { decide := true }) [σ2, σ1, σ0, start, Function.update])
  set σ3 := (σ2.seth J (head.length + ((ts.take c.val).map tri).flatten.length)).seth C c.val
  -- the three literal copies
  have hsplit := flatten_split ts c.val hc
  have hti : ts[c.val] = ((RepairSource.literalCode (raw.clause c 0)).bits, (RepairSource.literalCode (raw.clause c 1)).bits,
      (RepairSource.literalCode (raw.clause c 2)).bits) := by simp [ts, triples]
  set pre := head ++ ((ts.take c.val).map tri).flatten
  set post := ((ts.drop (c.val+1)).map tri).flatten
  have hJ3 : σ3.st J = pre ++ frame (RepairSource.literalCode (raw.clause c 0)).bits ++
      (frame (RepairSource.literalCode (raw.clause c 1)).bits ++ frame (RepairSource.literalCode (raw.clause c 2)).bits ++ post) := by
    simp (config := { decide := true }) only [σ3, σ2, σ1, σ0, WState.seth_st, WState.sets_st, start,
      Function.update_apply, if_true, if_false]
    rw [hw, hsplit, hti]
    simp [tri, pre, post, head, List.append_assoc]
  have h4 := copy_exec (cap := cap) L0 A2 (by decide) (by decide) (by decide) σ3 pre _ _ hJ3
    (by simp (config := { decide := true }) [σ3, pre, Function.update]) (by simp (config := { decide := true }) [σ3, σ2, σ1, σ0, start, Function.update]) (by simp (config := { decide := true }) [σ3, σ2, σ1, σ0, start, Function.update])
    (by simp (config := { decide := true }) [σ3, σ2, σ1, σ0, start, Function.update]) (by simp (config := { decide := true }) [σ3, σ2, σ1, σ0, start, Function.update])
  set σ4 := ((σ3.seth J (pre.length + (frame (RepairSource.literalCode (raw.clause c 0)).bits).length)).sets L0
    (frame (RepairSource.literalCode (raw.clause c 0)).bits)).sets A2
    (List.replicate (frame (RepairSource.literalCode (raw.clause c 0)).bits).length false)
  have h5 := copy_exec (cap := cap) L1 A3 (by decide) (by decide) (by decide) σ4
    (pre ++ frame (RepairSource.literalCode (raw.clause c 0)).bits) (RepairSource.literalCode (raw.clause c 1)).bits
    (frame (RepairSource.literalCode (raw.clause c 2)).bits ++ post)
    (by simp (config := { decide := true }) only [σ4, WState.sets_st, WState.seth_st, Function.update_apply,
      if_true, if_false]; rw [hJ3]; simp [List.append_assoc])
    (by simp (config := { decide := true }) [σ4, Function.update]) (by simp (config := { decide := true }) [σ4, σ3, σ2, σ1, σ0, start, Function.update]) (by simp (config := { decide := true }) [σ4, σ3, σ2, σ1, σ0, start, Function.update])
    (by simp (config := { decide := true }) [σ4, σ3, σ2, σ1, σ0, start, Function.update]) (by simp (config := { decide := true }) [σ4, σ3, σ2, σ1, σ0, start, Function.update])
  set σ5 := ((σ4.seth J ((pre ++ frame (RepairSource.literalCode (raw.clause c 0)).bits).length +
    (frame (RepairSource.literalCode (raw.clause c 1)).bits).length)).sets L1
    (frame (RepairSource.literalCode (raw.clause c 1)).bits)).sets A3
    (List.replicate (frame (RepairSource.literalCode (raw.clause c 1)).bits).length false)
  have h6 := copy_exec (cap := cap) L2 A4 (by decide) (by decide) (by decide) σ5
    (pre ++ frame (RepairSource.literalCode (raw.clause c 0)).bits ++ frame (RepairSource.literalCode (raw.clause c 1)).bits)
    (RepairSource.literalCode (raw.clause c 2)).bits post
    (by simp (config := { decide := true }) only [σ5, σ4, WState.sets_st, WState.seth_st, Function.update_apply,
      if_true, if_false]; rw [hJ3]; simp [List.append_assoc])
    (by simp (config := { decide := true }) [σ5, σ4, Function.update]; omega) (by simp (config := { decide := true }) [σ5, σ4, σ3, σ2, σ1, σ0, start, Function.update]) (by simp (config := { decide := true }) [σ5, σ4, σ3, σ2, σ1, σ0, start, Function.update])
    (by simp (config := { decide := true }) [σ5, σ4, σ3, σ2, σ1, σ0, start, Function.update]) (by simp (config := { decide := true }) [σ5, σ4, σ3, σ2, σ1, σ0, start, Function.update])
  have hall := WXExec.seq h1 (WXExec.seq h2 (WXExec.seq h3 (WXExec.seq h4 (WXExec.seq h5 h6))))
  refine ⟨_, WXExec.mono hall ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hf : ∀ w : List Bool, (frame w).length ≤ W → 2 * (frame w).length + 2 ≤ 2 * W + 2 := fun w h => by omega
    have hWsplit : W = head.length + ((ts.map tri).flatten).length := by
      simp only [W]; rw [hw, List.length_append]
    have hh : head.length = (frame raw.proofBits.bits).length + (frame raw.randomBits.bits).length := by
      simp only [head, List.length_append]
    have e0 : (frame raw.proofBits.bits).length ≤ W := by omega
    have e1 : (frame raw.randomBits.bits).length ≤ W := by omega
    have hJlen : (σ3.st J).length = W := by
      simp (config := { decide := true }) only [σ3, σ2, σ1, σ0, WState.seth_st, WState.sets_st, start,
        Function.update_apply, if_true, if_false, W]
    have e2 : (frame (RepairSource.literalCode (raw.clause c 0)).bits).length ≤ W := by
      rw [← hJlen, hJ3]; simp only [List.length_append]; omega
    have e3 : (frame (RepairSource.literalCode (raw.clause c 1)).bits).length ≤ W := by
      rw [← hJlen, hJ3]; simp only [List.length_append]; omega
    have e4 : (frame (RepairSource.literalCode (raw.clause c 2)).bits).length ≤ W := by
      rw [← hJlen, hJ3]; simp only [List.length_append]; omega
    have := hf _ e0
    have := hf _ e1
    have := hf _ e2
    have := hf _ e3
    have := hf _ e4
    unfold cost
    nlinarith
  all_goals simp (config := { decide := true }) only [σ5, σ4, σ3, σ2, σ1, σ0, WState.seth_st, WState.sets_st,
    Function.update_apply, if_true, if_false, start]

/-- The cold entry bank of the rewound program: the word on tape 0, `c` in unary on tape 2, all else empty. -/
def bank (word : List Bool) (c : ℕ) : Fin (11 + 2 + 0 + 1) → List Bool :=
  fun j => if j.val = 0 then word else if j.val = 2 then List.replicate c true else []

theorem bank_eq (word : List Bool) (c : ℕ) :
    Fin.addCases (coldBank (start word c)) (fun _ => []) = bank word c := by
  funext j
  refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
  · rw [Fin.addCases_left]
    rcases WireExponent3_5.PrimAsm.DockW.tape_cases j' with ⟨i, rfl⟩ | rfl | ⟨q, _⟩
    · rw [coldBank_s]
      fin_cases i <;> simp (config := { decide := true }) [start, bank, sTape]
    · rw [coldBank_c]
      simp [bank, cTape]
    · exact q.elim0
  · rw [Fin.addCases_right]
    simp [bank]

open NearCubicGates.PublishedSources.PCPP in

theorem clause_ready {n : ℕ} (raw : RawThreeQueryPCPP n) (c : Fin (2 ^ raw.randomBits)) :
    ∃ out, ClockJoin.ReadyRun (Rewind.machine program.compile) (2 * cost raw.word.length c + 2)
      (bank raw.word c) out ∧
      out ((sTape (nr := 0) PB).castAdd 1) = frame raw.proofBits.bits ∧
      out ((sTape (nr := 0) RB).castAdd 1) = frame raw.randomBits.bits ∧
      out ((sTape (nr := 0) L0).castAdd 1) = frame (RepairSource.literalCode (raw.clause c 0)).bits ∧
      out ((sTape (nr := 0) L1).castAdd 1) = frame (RepairSource.literalCode (raw.clause c 1)).bits ∧
      out ((sTape (nr := 0) L2).castAdd 1) = frame (RepairSource.literalCode (raw.clause c 2)).bits := by
  obtain ⟨τ, h, hPB, hRB, h0, h1, h2⟩ := program_exec (cap := 0) raw c
  obtain ⟨out, hrun, hst⟩ := WXExec.readyRewound h (fun _ => rfl) (fun r => r.elim0) rfl
  rw [bank_eq] at hrun
  exact ⟨out, hrun, (hst PB).trans hPB, (hst RB).trans hRB, (hst L0).trans h0, (hst L1).trans h1,
    (hst L2).trans h2⟩

end ClauseAccess

end NearCubicGates.Close.CheckedPCPP
