import Proof.Wire_3_5.CompilerMachinePolyTermStep

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Poly
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.CompilerMachine.Unions NearCubicWires.WireExponent3_5.CompilerMachine.Cancel
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks NearCubicWires.WireExponent3_5.CompilerMachine.Bridge
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

def cbits (c : ℤ) : List Bool := decide (c < 0) :: Nat.bits c.natAbs

def termWord (t : ℤ × List (F2Poly ℕ)) : List Bool := frame (cbits t.1) ++ (t.2.flatMap factorRec ++ [false])

/-- A term's record in the expression. -/
def termRec (t : ℤ × List (F2Poly ℕ)) : List Bool := true :: termWord t

/-- One output group: a marker, the coefficient's frame, the parity frame, the unions entries, a terminator. -/
def groupWord (cb : List Bool) (par : Bool) (E : List (List Bool)) : List Bool :=
  [true] ++ frame cb ++ [true] ++ [par] ++ [false] ++ E.flatMap frame ++ [false]

/-- The pipeline state after the counter's pass over the term's factors (from the emptied running list). -/
def psAfter (Q : ℕ) (pool : List (List SynEq)) (j : ℕ) (t : ℤ × List (F2Poly ℕ)) (st : TS) : PS × Bool × ℕ :=
  t.2.foldl (f2i Q pool j) ({ st.ps with G := [], staleG := (streamTape st.ps.G st.ps.staleG).tail }, false, 0)

/-- The unions stage's final state. -/
def uAfter (Q : ℕ) (pool : List (List SynEq)) (j : ℕ) (t : ℤ × List (F2Poly ℕ)) (st : TS) : UState :=
  (psAfter Q pool j t st).1.G.foldl (ustep Q pool.flatten.length) ⟨[], st.Sp.tail, st.Op, st.Gw, st.Rp, st.Zu, st.Z2u, st.Cu⟩

/-- **The term state after one term** for the counter value `j`. -/
def termNext (Q : ℕ) (pool : List (List SynEq)) (j : ℕ) (st : TS) (t : ℤ × List (F2Poly ℕ)) : TS :=
  ⟨(psAfter Q pool j t st).1, (psAfter Q pool j t st).2.1, overlay (frame (cbits t.1)) st.CW,
    streamTape (uAfter Q pool j t st).E (uAfter Q pool j t st).staleS, (uAfter Q pool j t st).O,
    (uAfter Q pool j t st).g, (uAfter Q pool j t st).R, (uAfter Q pool j t st).Z, (uAfter Q pool j t st).Z2,
    (uAfter Q pool j t st).C,
    st.outs ++ [true] ++ frame (cbits t.1) ++ [true] ++ [(psAfter Q pool j t st).2.1] ++ [false] ++
      (uAfter Q pool j t st).E.flatMap frame ++ [false]⟩

/-- The term appends one group to the output. -/
theorem termNext_outs (Q : ℕ) (pool : List (List SynEq)) (j : ℕ) (st : TS) (t : ℤ × List (F2Poly ℕ)) :
    (termNext Q pool j st t).outs = st.outs ++ groupWord (cbits t.1) (psAfter Q pool j t st).2.1 (uAfter Q pool j t st).E := by
  simp [termNext, groupWord, List.append_assoc]

/-- Replace the unions tapes by a unions state. -/
def setU (st : TS) (u : UState) : TS :=
  { st with Sp := streamTape u.E u.staleS, Op := u.O, Gw := u.g, Rp := u.R, Zu := u.Z, Z2u := u.Z2, Cu := u.C }

/-- The uniform cost bound of one term: coefficient bits at most `CBW`, `m` factors, the unions of at most `NU` entries
over at most `NG` cancelled monomials. -/
def termCost (CBW m NF CB d P Q W B NG NU : ℕ) : ℕ :=
  2 * (2 * (2 * CBW + 1) + 2) + (2 * (1 + 1 + (m * (factorCost NF CB d P Q W B + 2) + 1)) + 2) +
    unionsCost NG NU (Q + W + 1) + (2 * (NU * (2 * (Q + W + 1) + 1 + 1 + 1 + 2) + 1) + 2) + 40

theorem term_run (Q : ℕ) (pool : List (List SynEq)) (t : ℤ × List (F2Poly ℕ)) (j m : ℕ) (P post staleT : List Bool)
    (x : TFix) (st : TS) (d B NF CB CBW NG NU o : ℕ)
    (hVT : x.VT = P ++ termRec t ++ post) (hTT : x.TT = tableTape (childTable Q pool) staleT)
    (hz : x.z = z0 Q pool.flatten.length) (hJt : x.Jt = frame (binary m j))
    (hT1 : x.T1 = lastT Q pool.flatten.length) (hT2 : x.T2 = levelT Q pool.flatten.length)
    (hZT : x.ZT = zeroT Q pool.flatten.length) (hQ : 1 ≤ Q) (hm : t.2.length = m)
    (hp : ∀ f ∈ t.2, ∀ mono ∈ f, ∀ a ∈ mono, a < pool.length) (hd : ∀ f ∈ t.2, ∀ mono ∈ f, mono.length ≤ d)
    (hNF : ∀ f ∈ t.2, f.length ≤ NF) (hCB : ∀ f ∈ t.2, ∀ mono ∈ f, (codeBits mono).length ≤ CB)
    (hinv : PInv (Q + pool.flatten.length + 1) st.ps) (hB : (t.2.flatten.flatMap (monoMasks pool)).length ≤ B)
    (hc : Caps d pool.length Q pool.flatten.length B x.cap x.cap2 x.cap3)
    (hcap4 : 1 + 1 + (m * (factorCost NF CB d pool.length Q pool.flatten.length B + 2) + 1) ≤ x.cap4)
    (hcw : (cbits t.1).length ≤ CBW) (hcwc : 2 * CBW + 1 ≤ x.cap)
    (hSp : st.Sp ≠ [])
    (hU : UInv (Q + pool.flatten.length + 1) ⟨[], st.Sp.tail, st.Op, st.Gw, st.Rp, st.Zu, st.Z2u, st.Cu⟩)
    (hNG : (psAfter Q pool j t st).1.G.length ≤ NG)
    (hNU : ((psAfter Q pool j t st).1.G.foldl (liftStepW Q pool.flatten.length) []).length ≤ NU)
    (hcap2u : pass1Cost NU (Q + pool.flatten.length + 1) ≤ x.cap2 ∧
      appendCost NU (NU + 1) (Q + pool.flatten.length + 1) ≤ x.cap2)
    (hcap3u : NG * (aCost NU (Q + pool.flatten.length + 1) + 2) + 1 ≤ x.cap3)
    (hcap3o : NU * (2 * (Q + pool.flatten.length + 1) + 1 + 1 + 1 + 2) + 1 ≤ x.cap3)
    (ho : o = st.outs.length) :
    Step termM (termCost CBW m NF CB d pool.length Q pool.flatten.length B NG NU) (tHead P.length o) (tBank x st)
      (tHead (P.length + (termRec t).length) (termNext Q pool j st t).outs.length) (tBank x (termNext Q pool j st t)) := by
  subst ho
  set cb := cbits t.1
  have hbr : st.Sp = st.Sp.head hSp :: st.Sp.tail := (List.cons_head_tail hSp).symm
  -- the coefficient
  have hVT1 : x.VT = (P ++ [true]) ++ frame cb ++ (t.2.flatMap factorRec ++ [false] ++ post) := by
    rw [hVT]; simp [termRec, termWord, List.append_assoc, cb]
  have s1 := tNudgeV_step x st P.length st.outs.length
  have s1' := s1.congr (hout' := tHead (P ++ [true]).length st.outs.length) (tout' := tBank x st)
    (by funext i; fin_cases i <;> simp [tHead]) rfl
  have s2 := tLoadCW_step x st (P ++ [true]) cb (t.2.flatMap factorRec ++ [false] ++ post) st.outs.length hVT1
    ((Nat.add_le_add_right (Nat.mul_le_mul_left 2 hcw) 1).trans hcwc)
  set st1 : TS := { st with CW := overlay (frame cb) st.CW }
  have s3 := tNudgeV_step x st1 ((P ++ [true]).length + 2 * cb.length) st.outs.length
  have s3' := s3.congr (hout' := tHead (P ++ [true] ++ frame cb).length st.outs.length) (tout' := tBank x st1)
    (by funext i; fin_cases i <;> simp [tHead, frame_length]; omega) rfl
  -- empty the running list and the parity cell
  have s4 := tClrG_step x st1 (P ++ [true] ++ frame cb).length st.outs.length
  set st2 : TS := { st1 with ps := { st1.ps with G := [], staleG := (streamTape st1.ps.G st1.ps.staleG).tail } }
  have s5 := tClrPJ_step x st2 (P ++ [true] ++ frame cb).length st.outs.length
  set st3 : TS := { st2 with PJ := false }
  -- the counter's pass over the factors
  have hVT2 : x.VT = (P ++ [true] ++ frame cb) ++ t.2.flatMap factorRec ++ false :: post := by
    rw [hVT]; simp [termRec, termWord, List.append_assoc, cb]
  obtain ⟨hR, hR2, hR3, hX, hY, _⟩ := hinv
  have s6 := tJB_step Q pool t.2 j m (P ++ [true] ++ frame cb) post staleT x st3 d B NF CB st.outs.length hVT2 hTT hz
    hJt hm hp hd hNF hCB ⟨hR, hR2, hR3, hX, hY, by intro g hg; simp [st3, st2] at hg⟩ (by simpa [st3, st2] using hB) hc
    hcap4
  set ps4 := (t.2.foldl (f2i Q pool j) (st3.ps, st3.PJ, 0))
  set st4 : TS := setPS st3 ps4.1 ps4.2.1
  have s7 := tNudgeV_step x st4 ((P ++ [true] ++ frame cb).length + (t.2.flatMap factorRec).length) st.outs.length
  -- the unions
  have s8 := tClrSp_step x st4 (st.Sp.head hSp) st.Sp.tail hbr
    ((P ++ [true] ++ frame cb).length + (t.2.flatMap factorRec).length + 1) st.outs.length
  set st5 : TS := { st4 with Sp := false :: st.Sp.tail }
  have hps4 : ps4 = psAfter Q pool j t st := rfl
  have hG4 : ∀ g ∈ ps4.1.G, g.length = (Q + pool.flatten.length + 1) := by
    have hfG := factors_G Q pool t.2 j st3.ps st3.PJ rfl hp
    intro g hg
    rw [hfG] at hg
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hg
    exact entryWord_length Q pool.flatten.length 0 u (by omega)
  have hU5 : UInv (Q + pool.flatten.length + 1) ⟨[], st.Sp.tail, st5.Op, st5.Gw, st5.Rp, st5.Zu, st5.Z2u, st5.Cu⟩ := hU
  have hNG' : st5.ps.G.length ≤ NG := hNG
  have hNU' : (st5.ps.G.foldl (liftStepW Q pool.flatten.length) []).length ≤ NU := hNU
  have s9 := tUn_step Q pool.flatten.length x st5 st.Sp.tail ((P ++ [true] ++ frame cb).length + (t.2.flatMap factorRec).length + 1)
    st.outs.length rfl hT1 hT2 hZT hQ hG4 hU5 hc.c1
    ⟨(pass1Cost_mono (Q + pool.flatten.length + 1) hNU').trans hcap2u.1,
      ((appendCost_mono_left _ (Q + pool.flatten.length + 1) hNU').trans (appendCost_mono NU (Q + pool.flatten.length + 1) (Nat.add_le_add_right hNU' 1))).trans hcap2u.2⟩
    (le_trans (Nat.add_le_add_right (Nat.mul_le_mul hNG' (Nat.add_le_add_right (by
      unfold aCost; have := liftCost_mono (Q + pool.flatten.length + 1) hNU'; omega) 2)) 1) hcap3u)
  set uf := st5.ps.G.foldl (ustep Q pool.flatten.length) ⟨[], st.Sp.tail, st5.Op, st5.Gw, st5.Rp, st5.Zu, st5.Z2u, st5.Cu⟩
  set st6 : TS := setU st5 uf
  set pE := (P ++ [true] ++ frame cb).length + (t.2.flatMap factorRec).length + 1
  -- the group
  have s10 := tPut_step x st6 true pE
  set st7 : TS := { st6 with outs := st6.outs ++ [true] }
  have s11 := tEmitCW_step x st7 cb (st.CW.drop (frame cb).length) rfl
    ((Nat.add_le_add_right (Nat.mul_le_mul_left 2 hcw) 1).trans hcwc) pE
  set st8 : TS := { st7 with outs := st7.outs ++ frame cb }
  have s12 := tPut_step x st8 true pE
  set st9 : TS := { st8 with outs := st8.outs ++ [true] }
  have s13 := tParity_step x st9 pE
  set st10 : TS := { st9 with outs := st9.outs ++ [st9.PJ] }
  have s14 := tPut_step x st10 false pE
  set st11 : TS := { st10 with outs := st10.outs ++ [false] }
  have hEu : uf.E = st5.ps.G.foldl (liftStepW Q pool.flatten.length) [] := foldl_ustep_E Q pool.flatten.length st5.ps.G _
  have hEw : ∀ r ∈ uf.E, r.length = (Q + pool.flatten.length + 1) := by
    have := (foldl_ustep_inv Q pool.flatten.length hQ st5.ps.G _ hG4 hU5).1
    exact this
  have hEn : uf.E.length ≤ NU := by rw [hEu]; exact hNU'
  have s15 := tApp_step x st11 uf.E uf.staleS (Q + pool.flatten.length + 1) pE rfl hEw (by omega)
    (le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hEn) 1) hcap3o)
  set st12 : TS := { st11 with outs := st11.outs ++ uf.E.flatMap frame }
  have s16 := tPut_step x st12 false pE
  have part1 := (((((s1'.seq s2).seq s3').seq s4).seq s5).seq s6).seq s7
  have part2 := (((((((s8.seq s9).seq s10).seq s11).seq s12).seq s13).seq s14).seq s15).seq s16
  have hall := part1.seq part2
  have hcu := unionsCost_mono (L := Q + pool.flatten.length + 1) hNG' hNU'
  refine (hall.enlarge (by
    unfold termCost
    have h1 := Nat.mul_le_mul_right (2 * (Q + pool.flatten.length + 1) + 1 + 1 + 1 + 2) hEn
    omega)).congr ?_ ?_
  · funext i; fin_cases i
    · show (P ++ [true] ++ frame cb).length + (t.2.flatMap factorRec).length + 1 = P.length + (termRec t).length
      have hcbl : cb.length = (cbits t.1).length := rfl
      simp only [termRec, termWord, List.length_append, List.length_cons, List.length_nil, frame_length]
      omega
    all_goals rfl
  · funext i; fin_cases i <;> rfl

end NearCubicWires.WireExponent3_5.CompilerMachine.Poly
