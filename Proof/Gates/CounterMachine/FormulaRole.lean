import Proof.Gates.CounterMachine.FormulaFac
import Proof.Gates.Codec.FieldInt

/-! # RG machine, part 13: the digit factors of one role

**`roleDig_spec`**: for `j = 0, …, J − 1` the factor `1 − (E_j^r − κ_{base+j})^{q−1}` (lem:residue-count, v2 1511;
table (a)'s digits, 1660–1666), the residues read in order from the residue stream `KV`. Every head except `KV`'s
and every scratch register end as before; `KV`'s head has moved past the `J` residues used. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_append)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp enc_length)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Codec
open NearCubicGates.Close.Interfaces.Formats (Tok tokWord toks)

variable {ns nr : ℕ} (cap : ℕ)

section Role
variable (S : Fin (ns + 1)) (F : Fin 24 ↪ Fin nr)

/-- The digit factors of a role. -/
def digFacs (o base q J : ℕ) (blocks : List (List ℤ)) (L ρs : List ℕ) : List (List Tok) :=
  (List.range J).map fun j => facToks (digToks o (fun s => blocks.getD s []) (fun i => (L.getD i 0 : ℤ)) j)
    (ρs.getD (base + j) 0 : ℤ) q

/-- The digit-factor loop of a role (`J` in `Jn`, counter `Kd`). -/
def roleDig (CW FA KV : Fin (ns + 1)) (Gr off LB LBF Jc Jp Q1 Kd Jn : Fin nr) : WM ns nr :=
  .seq (copyR Jn Kd (F 8))
  (.seq (repLoop Kd (.seq (facP S F KV Q1 (digP S F CW FA Gr off LB LBF Jc Jp)) (.inc Jc))) (WM.clear Jc))

theorem TCap.mid {σ : WState ns nr} {a b c : List Tok} {Λ : ℕ} (h : TCap cap F σ (a ++ b ++ c) Λ) :
    TCap cap F (emitT S F σ a) b Λ := TCap.left cap F (TCap.right cap S F (by rw [List.append_assoc] at h; exact h))

theorem flatten_take_succ {α : Type} (xs : List (List α)) (i : ℕ) (hi : i < xs.length) :
    (xs.take (i + 1)).flatten = (xs.take i).flatten ++ xs[i] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.flatten_append]; simp

theorem roleDig_spec (CW FA KV : Fin (ns + 1)) (hSC : S ≠ CW) (hFS : FA ≠ S) (hKS : KV ≠ S) (hCK : CW ≠ KV)
    (hFK : FA ≠ KV)
    (Gr off LB LBF Jc Jp Q1 Kd Jn : Fin nr)
    (hF : ∀ i : Fin 24, F i ∉ [Gr, off, LB, LBF, Jc, Jp, Q1, Kd, Jn])
    (hd : [Gr, off, LB, LBF, Jc, Jp, Q1, Kd, Jn].Nodup)
    (G J o base q lb lbf Λ : ℕ) (blocks : List (List ℤ)) (L ρs : List ℕ) (hb : ∀ b ∈ blocks, b.length = G)
    (hJ : J ≤ blocks.length) (hJL : J ≤ L.length + 1) (hρ : base + J ≤ ρs.length)
    (restC restF restK : List Bool) (σ : WState ns nr) (h : TRest S F σ)
    (hstC : σ.st CW = encI blocks.flatten ++ restC) (hshC : σ.sh CW = 0)
    (hstF : σ.st FA = encN L ++ restF) (hshF : σ.sh FA = 0)
    (hstK : σ.st KV = encN ρs ++ restK) (hshK : σ.sh KV = (encN (ρs.take base)).length)
    (hGv : σ.val Gr = G) (hov : σ.val off = o) (hLv : σ.val LB = lb) (hLFv : σ.val LBF = lbf)
    (hJcv : σ.val Jc = 0) (hJpv : σ.val Jp = 0) (hQv : σ.val Q1 = q - 1) (hKdv : σ.val Kd = 0) (hJnv : σ.val Jn = J)
    (hlb : (encI (blocks.take J).flatten).length ≤ lb) (hlbf : (encN (L.take (J - 1))).length ≤ lbf)
    (hJΛ : J ≤ Λ) (hoG : o + G ≤ Λ) (hlbΛ : lb ≤ Λ) (hlbfΛ : lbf ≤ Λ) (hqΛ : q - 1 ≤ Λ)
    (hz : ∀ b ∈ blocks, ∀ z ∈ b, natBitLength z.natAbs ≤ Λ) (hLΛ : ∀ x ∈ L, natBitLength x ≤ Λ)
    (hρΛ : ∀ x ∈ ρs, natBitLength x ≤ Λ)
    (hcap : TCap cap F σ (digFacs o base q J blocks L ρs).flatten Λ) :
    WExec cap (roleDig S F CW FA KV Gr off LB LBF Jc Jp Q1 Kd Jn) σ
      ((emitT S F σ (digFacs o base q J blocks L ρs).flatten).seth KV (encN (ρs.take (base + J))).length)
      (20000 * (Λ + 1) ^ 4) := by
  have hne : ∀ {a b : Fin 24}, a ≠ b → F a ≠ F b := fun h => F.injective.ne h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hd
  obtain ⟨⟨g1, g2, g3, g4, g5, g6, g7, g8⟩, ⟨o1, o2, o3, o4, o5, o6, o7⟩, ⟨l1, l2, l3, l4, l5, l6⟩,
    ⟨f1, f2, f3, f4, f5⟩, ⟨c1, c2, c3, c4⟩, ⟨p1, p2, p3⟩, ⟨q1, q2⟩, k1⟩ := hd
  have hFr : ∀ r ∈ [Gr, off, LB, LBF, Jc, Jp, Q1, Kd, Jn], ∀ i : Fin 24, F i ≠ r := fun r hr i e => hF i (e ▸ hr)
  have fG := hFr Gr (by simp)
  have fo := hFr off (by simp)
  have fL := hFr LB (by simp)
  have fLF := hFr LBF (by simp)
  have fJc := hFr Jc (by simp)
  have fJp := hFr Jp (by simp)
  have fQ := hFr Q1 (by simp)
  have fK := hFr Kd (by simp)
  have fJn := hFr Jn (by simp)
  set facs := digFacs o base q J blocks L ρs with hfacs
  have hlen : facs.length = J := by simp [hfacs, digFacs]
  -- the loop states
  let g : ℕ → WState ns nr := fun t =>
    (((emitT S F σ (facs.take t).flatten).seth KV (encN (ρs.take (base + t))).length).setv Jc t).setv Kd (J - t)
  have gval : ∀ t r, r ≠ F 7 → r ≠ F 16 → r ≠ Jc → r ≠ Kd → (g t).val r = σ.val r := fun t r a b c d => by
    simp only [g, WState.setv_val, WState.seth_val, Function.update_of_ne d, Function.update_of_ne c]
    exact emitT_val_ne S F r a b σ _
  -- 1. Kd := J
  have e1 := copyR_spec cap (v := Jn) (d := Kd) (t := F 8) (Ne.symm k1) (fJn 8).symm (fK 8).symm σ
    (h.zero S F 8 (by decide)) (by rw [hKdv, hJnv]; unfold TCap at hcap; omega)
  rw [hKdv, hJnv, Nat.zero_add] at e1
  have hg0 : σ.setv Kd J = g 0 := by
    simp only [g, List.take_zero, List.flatten_nil, Nat.add_zero, Nat.sub_zero]
    rw [emitT_nil S F σ h.pr.out, ← hshK, wseth_same, ← hJcv, wsetv_same]
  rw [hg0] at e1
  -- 2. the loop
  have hbody : ∀ i < J, WExec cap (.seq (facP S F KV Q1 (digP S F CW FA Gr off LB LBF Jc Jp)) (.inc Jc))
      ((g i).setv Kd (J - i - 1)) (g (i + 1)) (14000 * (Λ + 1) ^ 3) := by
    intro i hi
    set Y := (g i).setv Kd (J - i - 1) with hY
    have hYv : ∀ r, r ≠ F 7 → r ≠ F 16 → r ≠ Jc → r ≠ Kd → Y.val r = σ.val r := fun r a b c d => by
      rw [hY, WState.setv_val, Function.update_of_ne d]; exact gval i r a b c d
    have hYJc : Y.val Jc = i := by simp [hY, g, Function.update_of_ne c3]
    have hYst : ∀ X, X ≠ S → Y.st X = σ.st X := fun X hX => by
      simp only [hY, g, WState.setv_st, WState.seth_st]; exact emitT_st_ne S F X hX σ _
    have hYsh : ∀ X, X ≠ S → X ≠ KV → Y.sh X = σ.sh X := fun X hX hXK => by
      simp only [hY, g, WState.setv_sh, WState.seth_sh, Function.update_of_ne hXK]; exact emitT_sh_ne S F X hX σ _
    have hYK : Y.sh KV = (encN (ρs.take (base + i))).length := by simp [hY, g]
    have hYR : TRest S F Y := by
      rw [hY]; simp only [g]
      exact ((((h.emitT S F _).seth S F KV hKS _).setv S F Jc fJc _).setv S F Kd fK _).setv S F Kd fK _
    have hYe : Y = (((emitT S F σ (facs.take i).flatten).seth KV (encN (ρs.take (base + i))).length).setv Jc i).setv
        Kd (J - i - 1) := by rw [hY]; simp only [g]; rw [wsetv_setv]
    -- the token room
    have hsplit : facs.flatten = (facs.take i).flatten ++ (facs[i]'(by omega)) ++ (facs.drop (i + 1)).flatten := by
      rw [← flatten_take_succ facs i (by omega), ← List.flatten_append, List.take_append_drop]
    have cY : TCap cap F Y (facs[i]'(by omega)) Λ := by
      have := TCap.mid cap S F (a := (facs.take i).flatten) (by rw [← hsplit]; exact hcap)
      rw [hYe]; exact ((this.seth cap F KV _).setv cap F Jc fJc _).setv cap F Kd fK _
    have hfi : (facs[i]'(by omega)) = facToks (digToks o (fun s => blocks.getD s []) (fun i => (L.getD i 0 : ℤ)) i)
        (ρs.getD (base + i) 0 : ℤ) q := by simp [hfacs, digFacs]
    rw [hfi] at cY
    have hρi : base + i < ρs.length := by omega
    have hρg : ρs.getD (base + i) 0 = ρs[base + i] := List.getD_eq_getElem _ _ hρi
    rw [hρg] at cY
    set Y1 := emitT S F Y [Tok.const 1] with hY1
    have hY1v : ∀ r, r ≠ F 7 → r ≠ F 16 → Y1.val r = Y.val r := fun r a b => emitT_val_ne S F r a b Y _
    have hP := digP_run cap S F CW FA hSC hFS Gr off LB LBF Jc Jp fG fo fL fLF fJc fJp c1 f2 g5 o4 l3
      G i o lb lbf Λ blocks L hb (by omega) (by omega) restC restF Y1 (hYR.emitT S F _)
      (by rw [hY1, emitT_st_ne S F CW hSC.symm, hYst CW hSC.symm, hstC])
      (by rw [hY1, emitT_sh_ne S F CW hSC.symm, hYsh CW hSC.symm hCK, hshC])
      (by rw [hY1, emitT_st_ne S F FA hFS, hYst FA hFS, hstF])
      (by rw [hY1, emitT_sh_ne S F FA hFS, hYsh FA hFS hFK, hshF])
      (by rw [hY1v _ (fG 7).symm (fG 16).symm, hYv _ (fG 7).symm (fG 16).symm g4 g7, hGv])
      (by rw [hY1v _ (fo 7).symm (fo 16).symm, hYv _ (fo 7).symm (fo 16).symm o3 o6, hov])
      (by rw [hY1v _ (fL 7).symm (fL 16).symm, hYv _ (fL 7).symm (fL 16).symm l2 l5, hLv])
      (by rw [hY1v _ (fLF 7).symm (fLF 16).symm, hYv _ (fLF 7).symm (fLF 16).symm f1 f4, hLFv])
      (by rw [hY1v _ (fJc 7).symm (fJc 16).symm, hYJc])
      (by rw [hY1v _ (fJp 7).symm (fJp 16).symm, hYv _ (fJp 7).symm (fJp 16).symm (Ne.symm c1) p2, hJpv])
      (le_trans (encI_take_mono blocks (by omega)) hlb) (le_trans (encN_take_mono L (by omega)) hlbf)
      (by omega) hoG hlbΛ hlbfΛ hz hLΛ
      (by rw [hY1]; exact TCap.mid cap S F (a := [Tok.const 1]) (c := [Tok.const ((ρs[base + i] : ℕ) : ℤ),
            Tok.sub, Tok.pow (q - 1), Tok.sub]) (by simpa [facToks] using cY))
    have hsplitK := encN_split ρs (base + i) hρi
    have eF := facP_spec cap S F KV hKS Q1 fQ (digP S F CW FA Gr off LB LBF Jc Jp)
      (digToks o (fun s => blocks.getD s []) (fun i => (L.getD i 0 : ℤ)) i) ρs[base + i] q Λ (9000 * (Λ + 1) ^ 3)
      (encN (ρs.take (base + i))) (encN (ρs.drop (base + i + 1)) ++ restK) Y hYR
      (by rw [hYst KV hKS, hstK, hsplitK]; simp [List.append_assoc]) hYK
      (by rw [hYv _ (fQ 7).symm (fQ 16).symm (Ne.symm c2) q1, hQv]) hqΛ (hρΛ _ (List.getElem_mem hρi)) cY hP
    set ft := facToks (digToks o (fun s => blocks.getD s []) (fun i => (L.getD i 0 : ℤ)) i) (ρs[base + i] : ℤ) q
    set p' := (encN (ρs.take (base + i))).length + 2 * (natWord ρs[base + i]).length
    have eI := WExec.inc (cap := cap) Jc ((emitT S F Y ft).seth KV p') (by
      simp only [WState.seth_val]; rw [emitT_val_ne S F Jc (fJc 7).symm (fJc 16).symm, hYJc]
      unfold TCap at hcap; omega)
    refine WExec.cast cap (WExec.seq eF eI) ?_ ?_
    · have hp' : p' = (encN (ρs.take (base + (i + 1)))).length := by
        rw [show base + (i + 1) = base + i + 1 by ring, encN_take_succ ρs (base + i) hρi]
      have hT : (facs.take (i + 1)).flatten = (facs.take i).flatten ++ ft := by
        rw [flatten_take_succ facs i (by omega), hfi, hρg]
      simp only [g]
      rw [hT, ← emitT_append, hYe, ← hp', emitT_setv S F Kd (fK 7).symm (fK 16).symm,
        emitT_setv S F Jc (fJc 7).symm (fJc 16).symm, emitT_seth S F KV hKS,
        show J - (i + 1) = J - i - 1 by omega]
      generalize emitT S F (emitT S F σ (List.take i facs).flatten) ft = τ
      apply WState.eq
      · funext j; by_cases hj : j = KV
        · subst hj; simp
        · simp [Function.update_of_ne hj]
      · simp
      · funext r; by_cases rK : r = Kd
        · subst rK; simp [Function.update_of_ne (Ne.symm c3)]
        · by_cases rJ : r = Jc
          · subst rJ; simp [Function.update_of_ne c3]
          · simp [Function.update_of_ne rK, Function.update_of_ne rJ]
      · simp
    · have h3 : (Λ + 1) ^ 2 ≤ (Λ + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
      have h1 : 1 ≤ (Λ + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      nlinarith
  have e2 := repLoop_spec cap Kd _ J (14000 * (Λ + 1) ^ 3) g
    (fun t _ => by simp [g]) (by unfold TCap at hcap; omega) hbody
  have e3 := wclear_spec cap Jc J (g J) (by simp [g, Function.update_of_ne c3])
    (by simp [g, Function.update_of_ne c3]; unfold TCap at hcap; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ ?_
  · have htk : facs.take J = facs := by rw [List.take_of_length_le (by omega)]
    simp only [g, htk, Nat.sub_self]
    apply WState.eq
    · simp
    · simp
    · funext r; by_cases rJ : r = Jc
      · subst rJ; simp [emitT_val_ne S F _ (fJc 7).symm (fJc 16).symm, hJcv]
      · by_cases rK : r = Kd
        · subst rK; simp [Function.update_of_ne (Ne.symm c3), emitT_val_ne S F _ (fK 7).symm (fK 16).symm, hKdv]
        · simp [Function.update_of_ne rJ, Function.update_of_ne rK]
    · simp
  · have h4 : (Λ + 1) ^ 3 ≤ (Λ + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have h1 : 1 ≤ (Λ + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    have hJ1 : J * (14000 * (Λ + 1) ^ 3 + 4) ≤ (Λ + 1) * (14000 * (Λ + 1) ^ 3 + 4) := Nat.mul_le_mul_right _ (by omega)
    have : (Λ + 1) ^ 4 = (Λ + 1) * (Λ + 1) ^ 3 := by ring
    nlinarith

end Role

end NearCubicGates.Close.CounterMachine
