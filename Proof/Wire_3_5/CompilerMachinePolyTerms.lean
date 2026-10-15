import Proof.Wire_3_5.CompilerMachinePolyTermRun

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

/-- The widths of the term machine's registers and lists. -/
def TSInv (L : ℕ) (st : TS) : Prop :=
  PInv L st.ps ∧ st.Sp ≠ [] ∧ UInv L ⟨[], st.Sp.tail, st.Op, st.Gw, st.Rp, st.Zu, st.Z2u, st.Cu⟩

/-- **The running list after a term's counter pass is its cancelled polarized polynomial.** -/
theorem termNext_G (Q : ℕ) (pool : List (List SynEq)) (j : ℕ) (st : TS) (t : ℤ × List (F2Poly ℕ))
    (hp : ∀ f ∈ t.2, ∀ mono ∈ f, ∀ a ∈ mono, a < pool.length) :
    (psAfter Q pool j t st).1.G =
      (oddMasksM pool (selectBits t.2 j).flatten).map (fun U => ew Q pool.flatten.length (0, U)) :=
  factors_G Q pool t.2 j _ false rfl hp

/-- **The group's unions are those of the cancelled polarized polynomial.** -/
theorem termNext_E (Q : ℕ) (pool : List (List SynEq)) (j : ℕ) (st : TS) (t : ℤ × List (F2Poly ℕ)) (hQ : 1 ≤ Q)
    (hp : ∀ f ∈ t.2, ∀ mono ∈ f, ∀ a ∈ mono, a < pool.length) :
    (uAfter Q pool j t st).E =
      (unionsM Q (oddMasksM pool (selectBits t.2 j).flatten)).map (ew Q pool.flatten.length) := by
  unfold uAfter
  rw [foldl_ustep_E, termNext_G Q pool j st t hp, unionsM_words Q _ hQ]

theorem termNext_inv (Q : ℕ) (pool : List (List SynEq)) (j : ℕ) (st : TS) (t : ℤ × List (F2Poly ℕ)) (hQ : 1 ≤ Q)
    (hp : ∀ f ∈ t.2, ∀ mono ∈ f, ∀ a ∈ mono, a < pool.length) (h : TSInv (Q + pool.flatten.length + 1) st) :
    TSInv (Q + pool.flatten.length + 1) (termNext Q pool j st t) := by
  obtain ⟨⟨hR, hR2, hR3, hX, hY, _⟩, _, hU⟩ := h
  have hfold := foldl_f2i Q pool j t.2 { st.ps with G := [], staleG := (streamTape st.ps.G st.ps.staleG).tail } false 0
  simp only [pow_zero, Nat.div_one] at hfold
  have hsel := selectBits_sublist t.2 j
  obtain ⟨hinv1, _⟩ := foldl_f1_inv Q pool (selectBits t.2 j).flatten
    { st.ps with G := [], staleG := (streamTape st.ps.G st.ps.staleG).tail }
    (fun mono hmono a ha => by
      obtain ⟨f, hf, hmf⟩ := List.mem_flatten.mp hmono
      exact hp f (hsel.subset hf) mono hmf a ha) ⟨hR, hR2, hR3, hX, hY, by simp⟩
  have hG : ∀ g ∈ (psAfter Q pool j t st).1.G, g.length = Q + pool.flatten.length + 1 := by
    rw [termNext_G Q pool j st t hp]
    intro g hg
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hg
    exact entryWord_length Q _ 0 u (by omega)
  obtain ⟨_, hg, hU1⟩ := foldl_ustep_inv Q pool.flatten.length hQ (psAfter Q pool j t st).1.G
    ⟨[], st.Sp.tail, st.Op, st.Gw, st.Rp, st.Zu, st.Z2u, st.Cu⟩ hG hU
  refine ⟨?_, ?_, ⟨by simp, hg, hU1⟩⟩
  · show PInv _ (psAfter Q pool j t st).1
    unfold psAfter
    rw [hfold]
    exact hinv1
  · show streamTape _ _ ≠ []
    simp [streamTape]

theorem foldl_termNext_inv (Q : ℕ) (pool : List (List SynEq)) (j : ℕ) (hQ : 1 ≤ Q) :
    ∀ (V : IntExpression ℕ) (st : TS), (∀ t ∈ V, ∀ f ∈ t.2, ∀ mono ∈ f, ∀ a ∈ mono, a < pool.length) →
      TSInv (Q + pool.flatten.length + 1) st → TSInv (Q + pool.flatten.length + 1) (V.foldl (termNext Q pool j) st)
  | [], _, _, h => h
  | t :: V, st, hp, h => by
    rw [List.foldl_cons]
    exact foldl_termNext_inv Q pool j hQ V _ (fun t' ht' => hp t' (List.mem_cons_of_mem t ht'))
      (termNext_inv Q pool j st t hQ (hp t List.mem_cons_self) h)

theorem termRec_head (t : ℤ × List (F2Poly ℕ)) : ∃ l, termRec t = true :: l := ⟨_, rfl⟩

theorem terms_run (Q : ℕ) (pool : List (List SynEq)) (j m : ℕ) (V : IntExpression ℕ) (P post staleT : List Bool)
    (x : TFix) (st : TS) (d B NF CB CBW NG NU : ℕ)
    (hVT : x.VT = P ++ V.flatMap termRec ++ false :: post) (hTT : x.TT = tableTape (childTable Q pool) staleT)
    (hz : x.z = z0 Q pool.flatten.length) (hJt : x.Jt = frame (binary m j))
    (hT1 : x.T1 = lastT Q pool.flatten.length) (hT2 : x.T2 = levelT Q pool.flatten.length)
    (hZT : x.ZT = zeroT Q pool.flatten.length) (hQ : 1 ≤ Q) (hm : Padded m V)
    (hp : ∀ t ∈ V, ∀ f ∈ t.2, ∀ mono ∈ f, ∀ a ∈ mono, a < pool.length)
    (hd : ∀ t ∈ V, ∀ f ∈ t.2, ∀ mono ∈ f, mono.length ≤ d) (hNF : ∀ t ∈ V, ∀ f ∈ t.2, f.length ≤ NF)
    (hCB : ∀ t ∈ V, ∀ f ∈ t.2, ∀ mono ∈ f, (codeBits mono).length ≤ CB)
    (hB : ∀ t ∈ V, (t.2.flatten.flatMap (monoMasks pool)).length ≤ B)
    (hcw : ∀ t ∈ V, (cbits t.1).length ≤ CBW)
    (hNG : ∀ t ∈ V, (oddMasksM pool (selectBits t.2 j).flatten).length ≤ NG)
    (hNU : ∀ t ∈ V, (unionsM Q (oddMasksM pool (selectBits t.2 j).flatten)).length ≤ NU)
    (hc : Caps d pool.length Q pool.flatten.length B x.cap x.cap2 x.cap3)
    (hcap4 : 1 + 1 + (m * (factorCost NF CB d pool.length Q pool.flatten.length B + 2) + 1) ≤ x.cap4)
    (hcwc : 2 * CBW + 1 ≤ x.cap)
    (hcap2u : pass1Cost NU (Q + pool.flatten.length + 1) ≤ x.cap2 ∧
      appendCost NU (NU + 1) (Q + pool.flatten.length + 1) ≤ x.cap2)
    (hcap3u : NG * (aCost NU (Q + pool.flatten.length + 1) + 2) + 1 ≤ x.cap3)
    (hcap3o : NU * (2 * (Q + pool.flatten.length + 1) + 1 + 1 + 1 + 2) + 1 ≤ x.cap3)
    (hinv : TSInv (Q + pool.flatten.length + 1) st) :
    Step (StreamController.machine termM 0)
      (V.length * (termCost CBW m NF CB d pool.length Q pool.flatten.length B NG NU + 2) + 1)
      (tHead P.length st.outs.length) (tBank x st)
      (tHead (P.length + (V.flatMap termRec).length) (V.foldl (termNext Q pool j) st).outs.length)
      (tBank x (V.foldl (termNext Q pool j) st)) := by
  refine encRun termRec termRec_head termM 0 P V post (termNext Q pool j) st (fun s q => tHead q s.outs.length)
    (fun s => tBank x s) (fun _ => hVT) (fun _ _ => rfl)
    (termCost CBW m NF CB d pool.length Q pool.flatten.length B NG NU) ?_
  intro k hk
  have htk := List.getElem_mem hk
  have hst : (V.take (k + 1)).foldl (termNext Q pool j) st = termNext Q pool j ((V.take k).foldl (termNext Q pool j) st) V[k] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append]
    rfl
  obtain ⟨hinvk, hSpk, hUk⟩ := foldl_termNext_inv Q pool j hQ (V.take k) st
    (fun t ht => hp t (List.mem_of_mem_take ht)) hinv
  have hGk := termNext_G Q pool j ((V.take k).foldl (termNext Q pool j) st) V[k] (hp _ htk)
  have hNGk : (psAfter Q pool j V[k] ((V.take k).foldl (termNext Q pool j) st)).1.G.length ≤ NG := by
    rw [hGk, List.length_map]; exact hNG _ htk
  have hNUk : ((psAfter Q pool j V[k] ((V.take k).foldl (termNext Q pool j) st)).1.G.foldl
      (liftStepW Q pool.flatten.length) []).length ≤ NU := by
    rw [hGk, ← unionsM_words Q _ hQ, List.length_map]; exact hNU _ htk
  have hb := term_run Q pool V[k] j m (P ++ (V.take k).flatMap termRec) ((V.drop (k + 1)).flatMap termRec ++ false :: post)
    staleT x ((V.take k).foldl (termNext Q pool j) st) d B NF CB CBW NG NU _
    (by rw [hVT, enc_split termRec V k hk]; simp [List.append_assoc]) hTT hz hJt hT1 hT2 hZT hQ (hm _ htk) (hp _ htk)
    (hd _ htk) (hNF _ htk) (hCB _ htk) hinvk (hB _ htk) hc hcap4 (hcw _ htk) hcwc hSpk hUk hNGk hNUk hcap2u hcap3u
    hcap3o rfl
  rw [hst, enc_succ_length termRec V k hk]
  refine (hb.congr_in ?_ rfl).congr ?_ rfl
  · funext i; fin_cases i <;> simp [tHead]
  · funext i; fin_cases i <;> simp [tHead]
    all_goals omega

end NearCubicWires.WireExponent3_5.CompilerMachine.Poly
