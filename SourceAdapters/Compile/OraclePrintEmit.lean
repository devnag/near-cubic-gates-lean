import SourceAdapters.Compile.OraclePrintLoop
import SourceAdapters.Compile.OraclePrintCells

/-!
# Writing the circuit word from the node records

proof of `thm:short-pcp-ours`: the algorithm outputs the circuit `C^O_x` itself, i.e. the native word
`OracleOutput.word ⟨ell, C⟩ = natWord ell ++ natWord |nodes| ++ nodes.flatMap oracleNodeWord ++ natWord output`
(`Statement.lean:1500`). `printP` writes the header, then every node from its record in store `NS` (`emitNode`, which reads the oracle arguments straight from the store), then the output reference.
**`printP_spec`**: from node records equal to `C.nodes.flatMap nodeRec`, exactly `OracleOutput.word ⟨ell, C⟩`.
-/

namespace NearCubicGates.Adapters.Compile.OraclePrint

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.Bindings.MW20
open NearCubicGates.Close.Cells

set_option autoImplicit false

variable {C : Ctx}

/-- The printing phase. -/
def printP : St VV MM :=
  .seq (emitHeader ELR CNT) (.seq (.op (.rwM NS)) (.seq (.op (.zero IR))
    (.seq (.loop (.lt IR CNT) (.seq (.op (.rdM NS TGR)) (.seq (.op (.rdM NS LFR)) (.seq (.op (.rdM NS RTR))
      (.seq (emitNode TGR LFR RTR ELR NS) (.op (.inc IR)))))))
      (emitTrailer OUTR))))

theorem flatMap_split {α : Type} (l : List α) (f : α → List ℕ) (k : ℕ) :
    l.flatMap f = (l.take k).flatMap f ++ (l.drop k).flatMap f := by
  rw [← List.flatMap_append, List.take_append_drop]

theorem drop_flatMap {α : Type} (l : List α) (f : α → List ℕ) (k : ℕ) :
    (l.flatMap f).drop ((l.take k).flatMap f).length = (l.drop k).flatMap f := by
  conv_lhs => rw [flatMap_split l f k]
  exact List.drop_left

theorem drop_succ_cons {l rest : List ℕ} {n v : ℕ} (h : l.drop n = v :: rest) : l.drop (n + 1) = rest := by
  have : l.drop (n + 1) = (l.drop n).drop 1 := by rw [List.drop_drop]
  rw [this, h]; rfl

/-- The cost bound of the printing phase. -/
def printCost (ell N R B : ℕ) : ℕ := N * (nodeCost ell B + 12) + R + 120 * B + 200

theorem printP_spec {ell : ℕ} (C0 : OracleCircuit ell ell) (a : DS VV MM) (hc : Cst a)
    (hns : a.ram NS = C0.nodes.flatMap nodeRec) (hcnt : a.env CNT = C0.nodes.length) (hell : a.env ELR = ell)
    (hout : a.env OUTR = C0.output.val) (ho : a.out = []) (hW : 3 ≤ C.Wd) (harity : ell < 2 ^ C.Wd)
    (hBW : natBitLength (ell + C0.size + 5) + 2 < 2 ^ C.Wd) (hNW : C0.nodes.length + 1 < 2 ^ C.Wd) :
    Hx C printP a (fun b c => b.out = OracleOutput.word ⟨ell, C0⟩ ∧
      c ≤ printCost ell C0.nodes.length (a.rc NS) (natBitLength (ell + C0.size + 5))) := by
  set B := natBitLength (ell + C0.size + 5) with hB
  have hsz : C0.size = C0.nodes.length := rfl
  have hB1 : natBitLength ell ≤ B := natBitLength_mono (by omega)
  have hB2 : natBitLength C0.nodes.length ≤ B := natBitLength_mono (by omega)
  have hB3 : natBitLength C0.output.val ≤ B := natBitLength_mono (by have := C0.output.isLt; omega)
  refine Hx.seq' (Hx.ofHs (emitHeader_spec C0 ELR CNT (by decide) (by decide) a hc (by omega) B (by omega) hell hcnt
    hB1 hB2)) (fun b0 c0 ⟨hc0', e1, e2, e3, e4, e5, e6, e7, hc0, e9⟩ => ?_)
  have hfr0 : ∀ y : Fin VV, y ∉ fieldScratch → b0.env y = a.env y := e9
  refine Hx.seq' (Hx.ofHs (hs_rwM C NS b0)) (fun b1 c1 ⟨hc1, hb1⟩ => ?_)
  subst hb1
  refine Hx.seq' (Hx.ofHs (hs_zero C IR _)) (fun b2 c2 ⟨hc2, hb2⟩ => ?_)
  subst hb2
  set a1 := (b0.rew NS).set IR 0 with ha1
  -- registers kept by every node emission
  have kreg : ∀ y : Fin VV, y ∈ [vZ, v1, v2, ELR, CNT, OUTR] → y ∉ nodeScratch := by decide
  let I : ℕ → DS VV MM → ℕ → Prop := fun k x cc => x.out = streamWord C0 k ∧ x.ram NS = a.ram NS ∧
    x.rc NS = ((C0.nodes.take k).flatMap nodeRec).length ∧ x.env IR = k ∧ x.env CNT = C0.nodes.length ∧
    x.env ELR = ell ∧ x.env OUTR = C0.output.val ∧ Cst x ∧ cc ≤ k * (nodeCost ell B + 12)
  have step : ∀ k < C0.nodes.length, ∀ x cc, I k x cc → Cnd.eval x (.lt IR CNT) = true ∧
      Hx C (.seq (.op (.rdM NS TGR)) (.seq (.op (.rdM NS LFR)) (.seq (.op (.rdM NS RTR))
        (.seq (emitNode TGR LFR RTR ELR NS) (.op (.inc IR)))))) x (fun y c1 => I (k + 1) y (cc + c1 + 2)) := by
    intro k hk x cc ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9⟩
    refine ⟨by simp [Cnd.eval, x4, x5, hk], ?_⟩
    have hdrop : (x.ram NS).drop (x.rc NS) =
        [nodeTag C0.nodes[k], nodeLeft C0.nodes[k], nodeRight C0.nodes[k]] ++ nodeArgs C0.nodes[k] ++
          (C0.nodes.drop (k + 1)).flatMap nodeRec := by
      rw [x2, hns, x3, drop_flatMap, List.drop_eq_getElem_cons hk, List.flatMap_cons]
      rfl
    have hget : ∀ (m v : ℕ) (rest : List ℕ), (x.ram NS).drop m = v :: rest →
        m < (x.ram NS).length ∧ (x.ram NS).getD m 0 = v := by
      intro m v rest h
      have hl := congrArg List.length h
      rw [List.length_drop, List.length_cons] at hl
      refine ⟨by omega, ?_⟩
      have := congrArg (fun l => l.getD 0 0) h
      simp only [List.getD_cons_zero] at this
      rw [← this, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero]
    have d0 : (x.ram NS).drop (x.rc NS) = nodeTag C0.nodes[k] :: (nodeLeft C0.nodes[k] ::
        nodeRight C0.nodes[k] :: (nodeArgs C0.nodes[k] ++ (C0.nodes.drop (k + 1)).flatMap nodeRec)) := by
      rw [hdrop]; simp
    have d1 := drop_succ_cons d0
    have d2 := drop_succ_cons d1
    have d3 := drop_succ_cons d2
    obtain ⟨g0, v0⟩ := hget _ _ _ d0
    obtain ⟨g1, v1'⟩ := hget _ _ _ d1
    obtain ⟨g2, v2'⟩ := hget _ _ _ d2
    refine Hx.seq' (Hx.ofHs (hs_rdM C NS TGR x (by simpa using g0))) (fun y0 dd0 ⟨hd0, hy0⟩ => ?_)
    subst hy0
    set y1 := (x.set TGR ((x.ram NS).getD (x.rc NS) 0)).adv NS with hy1
    have hy1rc : y1.rc NS = x.rc NS + 1 := by rw [hy1]; simp [DS.adv]
    have hy1ram : y1.ram NS = x.ram NS := rfl
    refine Hx.seq' (Hx.ofHs (hs_rdM C NS LFR y1 (by rw [hy1rc, hy1ram]; exact g1))) (fun y2 dd1 ⟨hd1, hy2⟩ => ?_)
    subst hy2
    set y2 := (y1.set LFR ((y1.ram NS).getD (y1.rc NS) 0)).adv NS with hy2
    have hy2rc : y2.rc NS = x.rc NS + 2 := by rw [hy2]; simp [DS.adv, hy1rc]
    have hy2ram : y2.ram NS = x.ram NS := rfl
    refine Hx.seq' (Hx.ofHs (hs_rdM C NS RTR y2 (by rw [hy2rc, hy2ram, show x.rc NS + 2 = x.rc NS + 1 + 1 by omega]; exact g2))) (fun y3 dd2 ⟨hd2, hy3⟩ => ?_)
    subst hy3
    set y3 := (y2.set RTR ((y2.ram NS).getD (y2.rc NS) 0)).adv NS with hy3
    have hy3rc : y3.rc NS = x.rc NS + 3 := by rw [hy3]; simp [DS.adv, hy2rc]
    have hy3ram : y3.ram NS = x.ram NS := rfl
    have hy3env : ∀ z : Fin VV, z ≠ TGR → z ≠ LFR → z ≠ RTR → y3.env z = x.env z := fun z h1 h2 h3 => by
      rw [hy3, DS.adv_env', DS.set_env_ne _ _ h3, hy2, DS.adv_env', DS.set_env_ne _ _ h2, hy1, DS.adv_env',
        DS.set_env_ne _ _ h1]
    have hTG : y3.env TGR = nodeTag C0.nodes[k] := by
      rw [hy3, DS.adv_env', DS.set_env_ne _ _ (by decide), hy2, DS.adv_env', DS.set_env_ne _ _ (by decide), hy1,
        DS.adv_env', DS.set_env_self]
      exact v0
    have hLF : y3.env LFR = nodeLeft C0.nodes[k] := by
      rw [hy3, DS.adv_env', DS.set_env_ne _ _ (by decide), hy2, DS.adv_env', DS.set_env_self, hy1rc, hy1ram]; exact v1'
    have hRT : y3.env RTR = nodeRight C0.nodes[k] := by
      rw [hy3, DS.adv_env', DS.set_env_self, hy2rc, hy2ram, show x.rc NS + 2 = x.rc NS + 1 + 1 by omega]; exact v2'
    have hcy3 : Cst y3 := ⟨by rw [hy3env vZ (by decide) (by decide) (by decide), x8.z],
      by rw [hy3env v1 (by decide) (by decide) (by decide), x8.one], by rw [hy3env v2 (by decide) (by decide) (by decide), x8.two]⟩
    have hout3 : y3.out = streamWord C0 k := x1
    have hmem : nodeArgs C0.nodes[k] <+: (y3.ram NS).drop (y3.rc NS) := by
      rw [hy3ram, hy3rc, show x.rc NS + 3 = x.rc NS + 1 + 1 + 1 by omega, d3]; exact List.prefix_append _ _
    refine Hx.seq' (Hx.ofHs (emitNode_stream C0 k hk TGR LFR RTR ELR (by decide) (by decide) (by decide) (by decide)
      NS y3 hcy3 hW hout3 hTG hLF hRT (by rw [hy3env ELR (by decide) (by decide) (by decide), x6]) harity hmem hBW))
      (fun y4 dd3 ⟨hd3, n1, _, n2, n3, _, _, _, n8, n9⟩ => ?_)
    have hy4 : ∀ z : Fin VV, z ∉ nodeScratch → y4.env z = y3.env z := n9
    have hIR4 : y4.env IR = k := by rw [hy4 IR (by decide), hy3env IR (by decide) (by decide) (by decide), x4]
    refine Hx.mono' (Hx.ofHs (hs_inc C IR y4 (by rw [hIR4]; omega))) (fun y5 dd4 ⟨hd4, hy5⟩ => ?_)
    subst hy5
    have hk' : ∀ z : Fin VV, z ∉ nodeScratch → z ≠ TGR → z ≠ LFR → z ≠ RTR → z ≠ IR →
        (y4.set IR (y4.env IR + 1)).env z = x.env z := fun z h0 h1 h2 h3 h4 => by
      rw [DS.set_env_ne _ _ h4, hy4 z h0, hy3env z h1 h2 h3]
    refine ⟨by rw [DS.set_out, n1], by rw [DS.set_ram, n2, hy3ram, x2], ?_, by rw [DS.set_env_self, hIR4],
      by rw [hk' CNT (by decide) (by decide) (by decide) (by decide) (by decide), x5],
      by rw [hk' ELR (by decide) (by decide) (by decide) (by decide) (by decide), x6],
      by rw [hk' OUTR (by decide) (by decide) (by decide) (by decide) (by decide), x7],
      ⟨by rw [DS.set_env_ne _ _ (by decide), n8.z], by rw [DS.set_env_ne _ _ (by decide), n8.one],
        by rw [DS.set_env_ne _ _ (by decide), n8.two]⟩, ?_⟩
    · rw [DS.set_rc, n3, Function.update_self, hy3rc, x3, List.take_add_one, List.getElem?_eq_getElem hk,
        Option.toList_some, List.flatMap_append, List.length_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, nodeRec, List.length_append, List.length_cons,
        List.length_nil]
      omega
    · have : dd3 ≤ nodeCost ell B := hd3
      rw [Nat.succ_mul]
      omega
  have stop : ∀ x cc, I C0.nodes.length x cc → Cnd.eval x (.lt IR CNT) = false := by
    intro x cc ⟨_, _, _, x4, x5, _⟩
    simp [Cnd.eval, x4, x5]
  have hI0 : I 0 a1 0 := by
    refine ⟨?_, ?_, ?_, DS.set_env_self _ _ _, ?_, ?_, ?_, ?_, Nat.zero_le _⟩
    · rw [ha1, DS.set_out]
      show b0.out = _
      rw [e1, ho]; rfl
    · rw [ha1, DS.set_ram]
      show b0.ram NS = _
      rw [e3]
    · rw [ha1, DS.set_rc]; simp [DS.rew]
    · rw [ha1, DS.set_env_ne _ _ (by decide), DS.rew_env', hfr0 CNT (by decide), hcnt]
    · rw [ha1, DS.set_env_ne _ _ (by decide), DS.rew_env', hfr0 ELR (by decide), hell]
    · rw [ha1, DS.set_env_ne _ _ (by decide), DS.rew_env', hfr0 OUTR (by decide), hout]
    · exact ⟨by rw [ha1, DS.set_env_ne _ _ (by decide), DS.rew_env', hc0.z],
        by rw [ha1, DS.set_env_ne _ _ (by decide), DS.rew_env', hc0.one],
        by rw [ha1, DS.set_env_ne _ _ (by decide), DS.rew_env', hc0.two]⟩
  refine Hx.seq' (Hx.loopAcc (show Cnd.wf (Cnd.lt IR CNT) from (by decide : IR ≠ CNT)) I C0.nodes.length step stop
    a1 hI0) (fun b3 c3 ⟨cf, ⟨i1, _, _, _, _, _, i7, i8, i9⟩, hc3⟩ => ?_)
  refine Hx.mono' (Hx.ofHs (emitTrailer_spec C0 OUTR (by decide) b3 i8 (by omega) B (by omega) i7 hB3 i1))
    (fun b4 c4 ⟨hc4, t1, _⟩ => ⟨t1, ?_⟩)
  have hrc0 : b0.rc NS = a.rc NS := by rw [e4]
  rw [hrc0] at hc1
  unfold printCost
  omega

end NearCubicGates.Adapters.Compile.OraclePrint
