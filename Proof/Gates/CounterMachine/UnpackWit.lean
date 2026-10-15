import Proof.Gates.CounterMachine.UnpackParams

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_append)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp enc_length readNatM readNatM_spec)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Codec NearCubicGates.Close.Counter NearCubicGates.Close.Interfaces

variable {ns nr : ℕ} (cap : ℕ)

theorem appendO_comm (σ : WState ns nr) (a b : Fin (ns + 1)) (hab : a ≠ b) (OP : Fin nr) (u v : List Bool) :
    appendO (appendO σ a OP u) b OP v = appendO (appendO σ b OP v) a OP u := by
  apply WState.eq
  · funext j; by_cases ja : j = a
    · subst ja; simp [appendO, Function.update_of_ne hab]
    · by_cases jb : j = b
      · subst jb; simp [appendO, Function.update_of_ne (Ne.symm hab)]
      · simp [appendO, Function.update_of_ne ja, Function.update_of_ne jb]
  · funext j; by_cases ja : j = a
    · subst ja; simp [appendO, Function.update_of_ne hab]
    · by_cases jb : j = b
      · subst jb; simp [appendO, Function.update_of_ne (Ne.symm hab)]
      · simp [appendO, Function.update_of_ne ja, Function.update_of_ne jb]
  · funext r; by_cases r1 : r = OP
    · subst r1; simp [appendO]; ring
    · simp [appendO, Function.update_of_ne r1]
  · simp [appendO]

section Wit
variable (IN : Fin (ns + 1)) (Q : Fin 16 ↪ Fin nr)

/-- The coefficient fields of stage `s`. -/
def wBlk (c : Call) (wt : Wit c.n) (s : ℕ) : List ℕ :=
  (List.range (roleCount c.kind)).flatMap fun r => [(wt.coef s r).length] ++ (wt.coef s r).flatMap intN

theorem witN_blocks (c : Call) (p : Params) (wt : Wit c.n) :
    witN c p wt = [(coordsOf wt.I).length] ++ coordsOf wt.I ++ (List.range p.J).flatMap (wBlk c wt) := by
  unfold witN srList wBlk
  simp [List.flatMap_assoc, List.flatMap_map]

def stageP (Y1 Y3 : Fin (ns + 1)) (Pr : Fin nr) : WM ns nr :=
  .seq (scriptProg IN Q [.copyI Y1]) (.ifr Pr (scriptProg IN Q [.copyI Y3]) .skip)

/-- All the stages (count `J` in `RJ`, loop counter `K`). -/
def unWit (Y1 Y3 : Fin (ns + 1)) (Pr RJ K : Fin nr) : WM ns nr :=
  .seq (scriptProg IN Q [.skipC]) (.seq (copyR RJ K (Q 3)) (repLoop K (stageP IN Q Y1 Y3 Pr)))

theorem wBlk_eq (c : Call) (wt : Wit c.n) (s : ℕ) :
    wBlk c wt s = ([(wt.coef s 0).length] ++ (wt.coef s 0).flatMap intN) ++
      (if c.kind = .pair then [(wt.coef s 1).length] ++ (wt.coef s 1).flatMap intN else []) := by
  unfold wBlk roleCount
  cases hk : c.kind <;> simp [List.range_succ]

/-- **One stage.** -/
theorem stageP_spec (Y1 Y3 : Fin (ns + 1)) (h1 : IN ≠ Y1) (h3 : IN ≠ Y3) (h13 : Y1 ≠ Y3) (Pr : Fin nr)
    (hPr : ∀ i, Q i ≠ Pr) (c : Call) (wt : Wit c.n) (s : ℕ) (A B : List ℕ) (rest : List Bool) (σ : WState ns nr)
    (hσ : NatAt IN (A ++ wBlk c wt s ++ B) rest σ A.length) (hz : QZero Q σ)
    (hPv : σ.val Pr = if c.kind = .pair then 1 else 0) (hY1 : σ.sh Y1 = (σ.st Y1).length)
    (hY3 : σ.sh Y3 = (σ.st Y3).length) (Λ : ℕ) (hbits : ∀ y ∈ A ++ wBlk c wt s ++ B, natBitLength y + 2 ≤ Λ)
    (hlen : (A ++ wBlk c wt s ++ B).length ≤ Λ)
    (hrd : 2 ^ (natBitLength (wt.coef s 0).length + 1) ≤ Λ ∧ 2 ^ (natBitLength (wt.coef s 1).length + 1) ≤ Λ)
    (hcap : 40 * (Λ + 1) ^ 2 + 6 * (encN (A ++ wBlk c wt s ++ B)).length + σ.val (Q 15) ≤ cap) :
    WExec cap (stageP IN Q Y1 Y3 Pr) σ
      ((appendO (appendO σ Y1 (Q 15) (encN ((wt.coef s 0).flatMap intN))) Y3 (Q 15)
        (encN (if c.kind = .pair then (wt.coef s 1).flatMap intN else []))).seth IN (encN (A ++ wBlk c wt s)).length)
      (1000 * (Λ + 1) ^ 2) := by
  have hQ : ∀ {a b : Fin 16}, a ≠ b → Q a ≠ Q b := fun h => Q.injective.ne h
  set X0 := [(wt.coef s 0).length] ++ (wt.coef s 0).flatMap intN with hX0
  set X1 := (if c.kind = .pair then [(wt.coef s 1).length] ++ (wt.coef s 1).flatMap intN else []) with hX1
  have hw := wBlk_eq c wt s
  rw [← hX0, ← hX1] at hw
  rw [hw] at hσ hbits hlen hcap ⊢
  have e1 := script_spec cap IN Q rest Λ [.copyI Y1] [X0]
    (List.Forall₂.cons ⟨⟨_, rfl⟩, by simpa [FOp.ReadOK, hX0] using hrd.1⟩ List.Forall₂.nil) A (X1 ++ B) σ
    (natAt_congr IN rest (by simp [List.append_assoc]) hσ) hz (by simp [FOp.regs]) (by simp [FOp.regs])
    (fun Z hZ => by simp [FOp.strs] at hZ; subst hZ; exact ⟨h1, hY1⟩)
    (fun y hy => hbits y (by simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_append] at hy ⊢; tauto))
    (by simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append] at hlen ⊢; omega)
    (by have h2 := encN_le_mid A X0 (X1 ++ B)
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at h2 ⊢
        rw [show A ++ X0 ++ (X1 ++ B) = A ++ (X0 ++ X1) ++ B by simp [List.append_assoc]] at h2 ⊢
        nlinarith)
  rw [show scriptEff Q [.copyI Y1] [X0] σ = appendO σ Y1 (Q 15) (encN ((wt.coef s 0).flatMap intN)) by
    simp [scriptEff, FOp.eff, hX0]] at e1
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at e1
  set σ1 := (appendO σ Y1 (Q 15) (encN ((wt.coef s 0).flatMap intN))).seth IN (encN (A ++ X0)).length with hσ1
  have hst1 : σ1.st IN = σ.st IN := by simp [hσ1, appendO, Function.update_of_ne h1]
  have z1 : QZero Q σ1 := fun i hi => by
    simp [hσ1, appendO, Function.update_of_ne (hQ hi)]; exact hz i hi
  have hP1 : σ1.val Pr = if c.kind = .pair then 1 else 0 := by
    simp [hσ1, appendO, Function.update_of_ne (hPr 15).symm, hPv]
  have hY3' : σ1.sh Y3 = (σ1.st Y3).length := by
    simp [hσ1, appendO, Function.update_of_ne (Ne.symm h13), Function.update_of_ne (Ne.symm h3), hY3]
  by_cases hp : c.kind = .pair
  · have hX1e : X1 = [(wt.coef s 1).length] ++ (wt.coef s 1).flatMap intN := by rw [hX1, if_pos hp]
    have e2 := script_spec cap IN Q rest Λ [.copyI Y3] [X1]
      (List.Forall₂.cons ⟨⟨_, hX1e⟩, by simpa [FOp.ReadOK, hX1e] using hrd.2⟩ List.Forall₂.nil) (A ++ X0) B σ1
      ⟨by rw [hst1, hσ.1]; simp [List.append_assoc],
       by simp only [hσ1, WState.seth_sh, Function.update_self]; rw [take_prefix]⟩ z1
      (by simp [FOp.regs]) (by simp [FOp.regs])
      (fun Z hZ => by simp [FOp.strs] at hZ; subst hZ; exact ⟨h3, hY3'⟩)
      (fun y hy => hbits y (by simp only [List.flatten_cons, List.flatten_nil, List.append_nil,
        List.mem_append] at hy ⊢; tauto))
      (by simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append] at hlen ⊢; omega)
      (by have h2 := encN_le_mid (A ++ X0) X1 B
          have h3' := encN_le_mid A X0 (X1 ++ B)
          rw [show A ++ X0 ++ (X1 ++ B) = A ++ X0 ++ X1 ++ B by simp [List.append_assoc]] at h3'
          simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at h2 ⊢
          have : σ1.val (Q 15) = σ.val (Q 15) + (encN ((wt.coef s 0).flatMap intN)).length := by
            simp [hσ1, appendO]
          have h4 : (encN ((wt.coef s 0).flatMap intN)).length ≤ (encN X0).length := by
            rw [hX0, encN_append, List.length_append]; omega
          have h5 : (encN (A ++ X0 ++ X1 ++ B)).length = (encN (A ++ (X0 ++ X1) ++ B)).length := by
            simp [List.append_assoc]
          rw [this]; omega)
    rw [show scriptEff Q [.copyI Y3] [X1] σ1 = appendO σ1 Y3 (Q 15) (encN ((wt.coef s 1).flatMap intN)) by
      simp [scriptEff, FOp.eff, hX1e]] at e2
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at e2
    refine WExec.mono (WExec.seq e1 (WExec.cast cap (WExec.ifrT (by rw [hP1, if_pos hp]; omega) e2) ?_ le_rfl)) ?_
    · rw [hσ1, if_pos hp]
      apply WState.eq
      · funext j; by_cases jI : j = IN
        · subst jI; simp [appendO, Function.update_of_ne h1, Function.update_of_ne h3, List.append_assoc, hX1e]
        · simp [appendO, Function.update_apply, jI, Ne.symm h3, Ne.symm h13, h13, h3, h1, Ne.symm h1]
      · simp [appendO]
      · simp [appendO]
      · simp [appendO]
    · have : 1 ≤ (Λ + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      simp only [List.length_cons, List.length_nil]; omega
  · have hX1e : X1 = [] := by rw [hX1, if_neg hp]
    refine WExec.mono (WExec.seq e1 (WExec.cast cap (WExec.ifrF (by rw [hP1, if_neg hp]) (WExec.skip σ1)) ?_ le_rfl)) ?_
    · rw [hσ1, if_neg hp, hX1e]
      rw [show (encN ([] : List ℕ)) = [] from rfl]
      rw [appendO_nil' _ Y3 (Q 15) (by simp [appendO, Function.update_of_ne (Ne.symm h13), hY3])]
      simp
    · have : 1 ≤ (Λ + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      simp only [List.length_cons, List.length_nil]; omega

/-- The role-0 and role-1 coefficient fields of the first `t` stages. -/
def W0 (c : Call) (wt : Wit c.n) (t : ℕ) : List ℕ := (List.range t).flatMap fun s => (wt.coef s 0).flatMap intN
def W1 (c : Call) (wt : Wit c.n) (t : ℕ) : List ℕ :=
  (List.range t).flatMap fun s => if c.kind = .pair then (wt.coef s 1).flatMap intN else []

theorem appendO_nil'' (σ : WState ns nr) (o : Fin (ns + 1)) (OP : Fin nr) (ho : σ.sh o = (σ.st o).length) :
    appendO σ o OP (encN []) = σ := appendO_nil' σ o OP ho

theorem wBlks_len (c : Call) (wt : Wit c.n) (J : ℕ) : J ≤ ((List.range J).flatMap (wBlk c wt)).length := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append]
    have : 1 ≤ (wBlk c wt J).length := by
      rw [wBlk_eq]; simp
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]; omega

theorem W_le_Bk (c : Call) (wt : Wit c.n) (t : ℕ) :
    (encN (W0 c wt t)).length + (encN (W1 c wt t)).length ≤ (encN ((List.range t).flatMap (wBlk c wt))).length := by
  induction t with
  | zero => simp [W0, W1, encN]
  | succ t ih =>
    have hW0 : W0 c wt (t + 1) = W0 c wt t ++ (wt.coef t 0).flatMap intN := by simp [W0, List.range_succ]
    have hW1 : W1 c wt (t + 1) = W1 c wt t ++
        (if c.kind = .pair then (wt.coef t 1).flatMap intN else []) := by simp [W1, List.range_succ]
    have hB : (List.range (t + 1)).flatMap (wBlk c wt) = (List.range t).flatMap (wBlk c wt) ++ wBlk c wt t := by
      simp [List.range_succ]
    have hw : (encN ((wt.coef t 0).flatMap intN)).length +
        (encN (if c.kind = .pair then (wt.coef t 1).flatMap intN else [])).length ≤ (encN (wBlk c wt t)).length := by
      rw [wBlk_eq]
      by_cases hp : c.kind = .pair
      · simp only [hp, if_true, encN_append, List.length_append]; omega
      · simp only [hp, if_false, encN_append, List.length_append, List.append_nil]
        have : (encN ([] : List ℕ)).length = 0 := rfl
        omega
    rw [hW0, hW1, hB, encN_append, encN_append, encN_append, List.length_append, List.length_append,
      List.length_append]
    omega

theorem appendO_seth_setv (σ : WState ns nr) (o X : Fin (ns + 1)) (hoX : o ≠ X) (OP K : Fin nr) (hK : OP ≠ K)
    (a v : ℕ) (u : List Bool) :
    appendO ((σ.seth X a).setv K v) o OP u = ((appendO σ o OP u).seth X a).setv K v := by
  apply WState.eq
  · funext j; by_cases jo : j = o
    · subst jo; simp [appendO, Function.update_of_ne hoX]
    · by_cases jX : j = X
      · subst jX; simp [appendO, Function.update_of_ne jo]
      · simp [appendO, Function.update_of_ne jo, Function.update_of_ne jX]
  · funext j; simp [appendO]
  · funext r; by_cases rO : r = OP
    · subst rO; simp [appendO, Function.update_of_ne hK]
    · by_cases rK : r = K
      · subst rK; simp [appendO, Function.update_of_ne rO]
      · simp [appendO, Function.update_of_ne rO, Function.update_of_ne rK]
  · simp [appendO]

theorem seth_setv_seth (σ : WState ns nr) (X : Fin (ns + 1)) (K : Fin nr) (a b v : ℕ) :
    ((σ.seth X a).setv K v).seth X b = (σ.seth X b).setv K v := by
  apply WState.eq
  · funext j; by_cases jX : j = X
    · subst jX; simp
    · simp [Function.update_of_ne jX]
  · simp
  · simp
  · simp

/-- **The witness's coefficient lists unpacked.** -/
theorem unWit_spec (Y1 Y3 : Fin (ns + 1)) (h1 : IN ≠ Y1) (h3 : IN ≠ Y3) (h13 : Y1 ≠ Y3) (Pr RJ K : Fin nr)
    (hR : [Pr, RJ, K].Nodup) (hQR : ∀ i, Q i ∉ [Pr, RJ, K]) (c : Call) (p : Params) (wt : Wit c.n) (A B : List ℕ)
    (rest : List Bool) (σ : WState ns nr) (hσ : NatAt IN (A ++ witN c p wt ++ B) rest σ A.length) (hz : QZero Q σ)
    (hPv : σ.val Pr = if c.kind = .pair then 1 else 0) (hJ : σ.val RJ = p.J) (hK : σ.val K = 0)
    (hY1 : σ.sh Y1 = (σ.st Y1).length) (hY3 : σ.sh Y3 = (σ.st Y3).length) (Λ : ℕ)
    (hbits : ∀ y ∈ A ++ witN c p wt ++ B, natBitLength y + 2 ≤ Λ) (hlen : (A ++ witN c p wt ++ B).length ≤ Λ)
    (hrd : 2 ^ (natBitLength (coordsOf wt.I).length + 1) ≤ Λ ∧
      ∀ s < p.J, 2 ^ (natBitLength (wt.coef s 0).length + 1) ≤ Λ ∧ 2 ^ (natBitLength (wt.coef s 1).length + 1) ≤ Λ)
    (hcap : 40 * (Λ + 1) ^ 2 + 10 * (encN (A ++ witN c p wt ++ B)).length + σ.val (Q 15) ≤ cap) :
    WExec cap (unWit IN Q Y1 Y3 Pr RJ K) σ
      ((appendO (appendO σ Y1 (Q 15) (encN (W0 c wt p.J))) Y3 (Q 15) (encN (W1 c wt p.J))).seth IN
        (encN (A ++ witN c p wt)).length) (2000 * (Λ + 1) ^ 3) := by
  have hQ : ∀ {a b : Fin 16}, a ≠ b → Q a ≠ Q b := fun h => Q.injective.ne h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hR
  obtain ⟨⟨PJ, PK⟩, JK⟩ := hR
  have qr : ∀ i r, r ∈ [Pr, RJ, K] → Q i ≠ r := fun i r hr h => hQR i (h ▸ hr)
  have hz' : ∀ i : Fin 16, i ≠ 15 → σ.val (Q i) = 0 := hz
  have hw := witN_blocks c p wt
  rw [hw] at hσ hbits hlen hcap ⊢
  set co := coordsOf wt.I
  set Bk := fun t => (List.range t).flatMap (wBlk c wt) with hBk
  have hsplit : ∀ t < p.J, ∃ R, (List.range p.J).flatMap (wBlk c wt) = Bk t ++ wBlk c wt t ++ R := by
    intro t ht
    refine ⟨((List.range (p.J - (t + 1))).map (fun i => t + 1 + i)).flatMap (wBlk c wt), ?_⟩
    rw [show p.J = (t + 1) + (p.J - (t + 1)) by omega, List.range_add, List.flatMap_append, List.range_succ,
      List.flatMap_append, show t + 1 + (p.J - (t + 1)) - (t + 1) = p.J - (t + 1) by omega]
    simp [hBk, List.flatMap_map]
  -- 1. skip the coordinates
  have e1 := script_spec cap IN Q rest Λ [.skipC] [[co.length] ++ co]
    (List.Forall₂.cons ⟨⟨co, rfl⟩, by simpa [FOp.ReadOK] using hrd.1⟩ List.Forall₂.nil) A
    ((List.range p.J).flatMap (wBlk c wt) ++ B) σ
    (natAt_congr IN rest (by simp [List.append_assoc]) hσ) hz (by simp [FOp.regs]) (by simp [FOp.regs])
    (by simp [FOp.strs])
    (fun y hy => hbits y (by simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_append] at hy ⊢; tauto))
    (by simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append] at hlen ⊢; omega)
    (by have h2 := encN_le_mid A ([co.length] ++ co) ((List.range p.J).flatMap (wBlk c wt) ++ B)
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at h2 ⊢
        rw [show A ++ ([co.length] ++ co) ++ ((List.range p.J).flatMap (wBlk c wt) ++ B) =
          A ++ ([co.length] ++ co ++ (List.range p.J).flatMap (wBlk c wt)) ++ B by simp [List.append_assoc]] at h2 ⊢
        omega)
  simp only [scriptEff, FOp.eff, List.flatten_cons, List.flatten_nil, List.append_nil] at e1
  set Pre := A ++ ([co.length] ++ co) with hPre
  -- 2. K := J
  have e2 := copyR_spec cap (v := RJ) (d := K) (t := Q 3) JK (qr 3 RJ (by simp)).symm (qr 3 K (by simp)).symm
    (σ.seth IN (encN Pre).length) (by simp; exact hz' 3 (by decide))
    (by simp [hK, hJ]; have := wBlks_len c wt p.J
        simp only [List.length_append] at hlen; nlinarith)
  simp only [WState.seth_val, hK, hJ, Nat.zero_add] at e2
  -- 3. the stages
  let g : ℕ → WState ns nr := fun t =>
    ((appendO (appendO σ Y1 (Q 15) (encN (W0 c wt t))) Y3 (Q 15) (encN (W1 c wt t))).seth IN
      (encN (Pre ++ Bk t)).length).setv K (p.J - t)
  have hg0 : (σ.seth IN (encN Pre).length).setv K p.J = g 0 := by
    simp only [g, W0, W1, List.range_zero, List.flatMap_nil, Nat.sub_zero, hBk, List.append_nil]
    rw [appendO_nil'' σ Y1 (Q 15) hY1, appendO_nil'' σ Y3 (Q 15) hY3]
  rw [hg0] at e2
  have hbody : ∀ t < p.J, WExec cap (stageP IN Q Y1 Y3 Pr) ((g t).setv K (p.J - t - 1)) (g (t + 1))
      (1000 * (Λ + 1) ^ 2) := by
    intro t ht
    obtain ⟨R, hR⟩ := hsplit t ht
    simp only [g]
    rw [wsetv_setv]
    set Z := (appendO (appendO σ Y1 (Q 15) (encN (W0 c wt t))) Y3 (Q 15) (encN (W1 c wt t))) with hZ
    have hZst : ∀ X, X ≠ Y1 → X ≠ Y3 → Z.st X = σ.st X := fun X a b => by
      simp [hZ, appendO, Function.update_of_ne a, Function.update_of_ne b]
    have hZv : ∀ r, r ≠ Q 15 → Z.val r = σ.val r := fun r hr => by simp [hZ, appendO, Function.update_of_ne hr]
    have e := stageP_spec cap IN Q Y1 Y3 h1 h3 h13 Pr (fun i => qr i Pr (by simp)) c wt t (Pre ++ Bk t) (R ++ B) rest
      ((Z.seth IN (encN (Pre ++ Bk t)).length).setv K (p.J - t - 1))
      ⟨by simp only [WState.setv_st, WState.seth_st]; rw [hZst IN h1 h3, hσ.1, hR]; simp [hPre, List.append_assoc],
       by simp only [WState.setv_sh, WState.seth_sh, Function.update_self]; rw [take_prefix]⟩
      (fun i hi => by
        simp only [WState.setv_val, WState.seth_val, Function.update_of_ne (qr i K (by simp))]
        rw [hZv _ (fun h => hi (Q.injective h))]; exact hz i hi)
      (by simp only [WState.setv_val, WState.seth_val, Function.update_of_ne PK]
          rw [hZv _ (Ne.symm (qr 15 Pr (by simp)))]; exact hPv)
      (by simp [hZ, appendO, Function.update_of_ne (Ne.symm h1), Function.update_of_ne h13, hY1])
      (by simp [hZ, appendO, Function.update_of_ne (Ne.symm h3), Function.update_of_ne (Ne.symm h13), hY3]) Λ
      (fun y hy => hbits y (by
        have : y ∈ Pre ++ Bk t ++ wBlk c wt t ++ (R ++ B) := hy
        rw [show Pre ++ Bk t ++ wBlk c wt t ++ (R ++ B) = Pre ++ (Bk t ++ wBlk c wt t ++ R) ++ B by
          simp [List.append_assoc], ← hR] at this
        simpa [hPre, List.append_assoc] using this))
      (by have := hlen; rw [hR] at this; simp only [hPre, List.length_append] at this ⊢; omega)
      (hrd.2 t ht)
      (by have hZ15 : Z.val (Q 15) = σ.val (Q 15) + (encN (W0 c wt t)).length + (encN (W1 c wt t)).length := by
            simp [hZ, appendO]
          simp only [WState.setv_val, WState.seth_val, Function.update_of_ne (qr 15 K (by simp))]
          rw [hZ15]
          have hW : (encN (W0 c wt t)).length + (encN (W1 c wt t)).length ≤ (encN (Bk t)).length := W_le_Bk c wt t
          have hm := encN_le_mid Pre (Bk t) (wBlk c wt t ++ R ++ B)
          have hl : Pre ++ Bk t ++ wBlk c wt t ++ (R ++ B) = Pre ++ (List.range p.J).flatMap (wBlk c wt) ++ B := by
            rw [hR]; simp [List.append_assoc]
          rw [show Pre ++ Bk t ++ (wBlk c wt t ++ R ++ B) = Pre ++ Bk t ++ wBlk c wt t ++ (R ++ B) by
            simp [List.append_assoc], hl] at hm
          rw [hl]
          have : (encN (A ++ ([co.length] ++ co ++ (List.range p.J).flatMap (wBlk c wt)) ++ B)).length =
              (encN (Pre ++ (List.range p.J).flatMap (wBlk c wt) ++ B)).length := by simp [hPre, List.append_assoc]
          omega)
    refine WExec.cast cap e ?_ le_rfl
    rw [appendO_seth_setv _ _ _ (Ne.symm h1) _ _ (qr 15 K (by simp)),
      appendO_seth_setv _ _ _ (Ne.symm h3) _ _ (qr 15 K (by simp)), seth_setv_seth, hZ,
      appendO_comm _ Y3 Y1 (Ne.symm h13), appendO_append, appendO_append]
    have hW0 : W0 c wt (t + 1) = W0 c wt t ++ (wt.coef t 0).flatMap intN := by simp [W0, List.range_succ]
    have hW1 : W1 c wt (t + 1) = W1 c wt t ++
        (if c.kind = .pair then (wt.coef t 1).flatMap intN else []) := by simp [W1, List.range_succ]
    have hB : Bk (t + 1) = Bk t ++ wBlk c wt t := by simp [hBk, List.range_succ]
    rw [hW0, hW1, hB, show p.J - t - 1 = p.J - (t + 1) by omega]
    simp only [encN_append, List.append_assoc]
  have hJl : p.J ≤ Λ := by
    have := wBlks_len c wt p.J
    simp only [List.length_append] at hlen; omega
  have hΛ : 1 ≤ (Λ + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have e3 := repLoop_spec cap K (stageP IN Q Y1 Y3 Pr) p.J (1000 * (Λ + 1) ^ 2) g
    (fun i _ => by simp [g]) (by nlinarith) hbody
  have hfin : g p.J = (appendO (appendO σ Y1 (Q 15) (encN (W0 c wt p.J))) Y3 (Q 15) (encN (W1 c wt p.J))).seth IN
      (encN (A ++ ([co.length] ++ co ++ (List.range p.J).flatMap (wBlk c wt)))).length := by
    simp only [g, Nat.sub_self]
    have hK0 : ((appendO (appendO σ Y1 (Q 15) (encN (W0 c wt p.J))) Y3 (Q 15) (encN (W1 c wt p.J))).seth IN
        (encN (Pre ++ Bk p.J)).length).val K = 0 := by
      simp [appendO, Function.update_of_ne (qr 15 K (by simp)).symm, hK]
    rw [show (encN (A ++ ([co.length] ++ co ++ (List.range p.J).flatMap (wBlk c wt)))).length =
      (encN (Pre ++ Bk p.J)).length by simp [hPre, hBk, List.append_assoc], ← hK0]
    apply WState.eq <;> simp
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) hfin ?_
  have h3 : p.J * (1000 * (Λ + 1) ^ 2 + 4) ≤ Λ * (1000 * (Λ + 1) ^ 2 + 4) := Nat.mul_le_mul_right _ hJl
  have h4 : (Λ + 1) ^ 3 = (Λ + 1) * (Λ + 1) ^ 2 := by ring
  simp only [List.length_cons, List.length_nil]
  nlinarith

end Wit

end NearCubicGates.Close.CounterMachine
