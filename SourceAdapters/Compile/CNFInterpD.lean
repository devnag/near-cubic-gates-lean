import SourceAdapters.Compile.CNFInterpC

/-!
# Token interpreter, part D: constant, input and negation tokens

`nodeTail_spec`: once the operands are popped and the node's clauses appended, pushing the node index and
incrementing it re-establishes `IR` for `S.push st x`. The constant, input and negation tokens realize `RS.step`
on `.cst`, `.inp`, `.neg` (`cstTokP_spec`, `inpTokP_spec`, `negTokP_spec`).
-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells NearCubicWires.TseitinCNF NearCubicWires.CircuitInputCNF
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

variable {C : Ctx}

/-- The registers a node token may change before `nodeEndP`. -/
def preT : List (Fin VV) := [iS, iJ, iSp, iY, iX, iG, c0, c1, c2, c3, c4, c5, c6]

theorem nodeTail_spec (n k : ℕ) (S : RS) (a b4 : DS VV MM) (h : IR n k S a) (hW : 64 * (n + k) + 64 ≤ 2 ^ C.Wd)
    (st : List ℕ) (x : RNode) (hst : ∀ y ∈ st, y ∈ S.stk) (hstl : st.length ≤ S.stk.length)
    (k4 : KC b4) (s4 : StkRel b4 st) (r4 : b4.ram sSK = a.ram sSK)
    (cl4 : b4.ram sCL = a.ram sCL ++ (rcl n S.idx x).map Encodable.encode)
    (clr4 : b4.rc sCL = a.rc sCL + ((rcl n S.idx x).map Encodable.encode).length)
    (u4 : ∀ m, m ≠ sSK → m ≠ sCL → b4.ram m = a.ram m ∧ b4.rc m = a.rc m)
    (i4 : b4.ip = a.ip) (o4 : b4.out = a.out) (f4 : Fr a b4 preT) :
    Hs C nodeEndP b4 (b4.rc sSK + 5 * st.length + 12) (fun b => IR n (k + 1) (S.push st x) b ∧
      (∀ m, m ≠ sSK → m ≠ sCL → b.ram m = a.ram m ∧ b.rc m = a.rc m) ∧ b.ip = a.ip ∧ b.out = a.out ∧
      Fr a b irT) := by
  have hidx := h.bidx
  have hS := h.nodes
  have hstkk : S.stk.length ≤ k := by have := h.stk.len; have := h.bsk; omega
  have b4idx : b4.env iIdx = S.idx := by rw [f4 iIdx (by decide), h.idx]
  refine Hs.seqc (t1 := b4.rc sSK + 5 * st.length + 10) (t2 := 1) (pushP_spec (C := C) iIdx (by decide) b4 st
    s4 (by omega)) (fun b5 hb5 => ?_) (by omega)
  obtain ⟨s5, l5, c5', u5, i5, o5, f5⟩ := hb5
  rw [b4idx] at s5
  have b5idx : b5.env iIdx = S.idx := by rw [f5 iIdx (by decide), b4idx]
  refine Hs.op (OpEx.inc iIdx b5 (by rw [b5idx]; omega)) ?_
  have fa : ∀ y, y ∉ preT → y ≠ iIdx → b5.env y = a.env y := fun y hy hi => by
    have hy' := hy
    simp only [preT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy'
    rw [f5 y (by simp [hy'.1, hy'.2.1, hy'.2.2.1]), f4 y hy]
  have k5 : KC b5 := k4.of_fr f5 (by decide)
  have hCL5 : b5.ram sCL = b4.ram sCL := (u5 sCL (by decide)).1
  have hCLr5 : b5.rc sCL = b4.rc sCL := (u5 sCL (by decide)).2
  have hram : ∀ m, m ≠ sSK → m ≠ sCL → b5.ram m = a.ram m := fun m h1 h2 => by
    rw [(u5 m h1).1, (u4 m h1 h2).1]
  have hrc : ∀ m, m ≠ sSK → m ≠ sCL → b5.rc m = a.rc m := fun m h1 h2 => by
    rw [(u5 m h1).2, (u4 m h1 h2).2]
  have hnodes : (circuitInputTautologies n ++ rclFrom n 0 (S.nodes ++ [x])).map Encodable.encode =
      (circuitInputTautologies n ++ rclFrom n 0 S.nodes).map Encodable.encode ++
        (rcl n S.idx x).map Encodable.encode := by
    rw [rclFrom_concat, hS]; simp
  refine ⟨⟨k5.of_fr (Fr.set (T := [iIdx]) b5 _ (by simp)) (by decide), ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [DS.set_env_ne _ _ (by decide), fa dN (by decide) (by decide), h.dn]
  · rw [DS.set_env_self, b5idx]; rfl
  · simp [RS.push, hS]
  · rw [DS.set_env_ne _ _ (by decide)]; exact s5.sp
  · exact s5.take
  · exact s5.len
  · rw [DS.set_env_ne _ _ (by decide), fa iWl (by decide) (by decide), h.wl]; rfl
  · simp only [DS.set_ram, RS.push]; rw [hram sWM (by decide) (by decide)]; exact h.wires
  · simp only [DS.set_ram, RS.push]; rw [hram sWM (by decide) (by decide)]; exact h.wlen
  · rw [DS.set_env_ne _ _ (by decide), fa iNc (by decide) (by decide), h.nc]; rfl
  · simp only [DS.set_ram, RS.push]; rw [hram sNW (by decide) (by decide)]; exact h.next
  · simp only [DS.set_ram, RS.push]; rw [hram sNW (by decide) (by decide)]; exact h.nlen
  · simp only [DS.set_rc, RS.push]; rw [hrc sNW (by decide) (by decide)]; exact h.rcnw
  · simp only [DS.set_ram, RS.push]; rw [hCL5, cl4, h.cl, hnodes]
  · simp only [DS.set_ram, DS.set_rc]; rw [hCL5, hCLr5, cl4, clr4, h.rccl]; simp
  · simp only [DS.set_ram]; have := s5.len; rw [r4] at l5; have := h.bsk; simp at this ⊢; omega
  · simp only [DS.set_ram, DS.set_rc]; rw [c5']; have := s5.len; simp at this ⊢; omega
  · simp only [DS.set_ram]; rw [hram sWM (by decide) (by decide)]; have := h.bwm; omega
  · simp only [DS.set_ram, DS.set_rc]; rw [hram sWM (by decide) (by decide), hrc sWM (by decide) (by decide)]
    exact h.rwm
  · simp only [DS.set_ram]; rw [hram sNW (by decide) (by decide)]; have := h.bnw; omega
  · simp only [RS.push]; omega
  · intro y hy
    simp only [RS.push, List.mem_cons] at hy
    rcases hy with hy | hy
    · omega
    · have := h.vstk y (hst y hy); omega
  · intro y hy; have := h.vwires y hy; omega
  · intro y hy; have := h.vnext y hy; omega
  · intro m h1 h2; exact ⟨by simp [hram m h1 h2], by simp [hrc m h1 h2]⟩
  · simp only [DS.set_ip]; rw [i5, i4]
  · simp only [DS.set_out]; rw [o5, o4]
  · intro y hy
    simp only [irT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [DS.set_env_ne _ _ hy.1]
    exact fa y (by simp [preT]; tauto) hy.1

/-! ## Constant and input tokens -/

/-- `iG := n + idx`. -/
def gateP : St VV MM := .seq (.op (.copy iG dN)) (.op (.add iG iIdx))

theorem gateP_spec (n k : ℕ) (S : RS) (a : DS VV MM) (h : IR n k S a) (hW : 64 * (n + k) + 64 ≤ 2 ^ C.Wd) :
    Hs C gateP a 3 (fun b => b.env iG = n + S.idx ∧ b.ram = a.ram ∧ b.rc = a.rc ∧ b.ip = a.ip ∧ b.out = a.out ∧
      Fr a b [iG]) := by
  have hidx := h.bidx
  apply hs_of_wpc
  simp only [gateP, wpc, opwp]
  vsimp [h.dn, h.idx]
  and_split
  all_goals first | omega | rfl | fr_tac | skip

/-- A nullary node token. -/
def nulTokP (cl : St VV MM) : St VV MM := .seq gateP (.seq cl nodeEndP)

theorem nulTokP_spec (cl : St VV MM) (tc : ℕ) (x : RNode) (n k : ℕ) (S : RS) (a : DS VV MM) (h : IR n k S a)
    (hW : 64 * (n + k) + 64 ≤ 2 ^ C.Wd)
    (hcl : ∀ b : DS VV MM, b.env vZ = 0 → b.env v1 = 1 → b.rc sCL = (b.ram sCL).length →
      b.env iG = n + S.idx → (∀ y, y ≠ iG → b.env y = a.env y) →
      Hs C cl b tc (fun d => ExtS sCL b d ((rcl n S.idx x).map Encodable.encode) ∧ Fr b d clT)) :
    Hs C (nulTokP cl) a (a.rc sSK + 6 * k + tc + 20) (fun b => IR n (k + 1) (S.push S.stk x) b ∧
      (∀ m, m ≠ sSK → m ≠ sCL → b.ram m = a.ram m ∧ b.rc m = a.rc m) ∧ b.ip = a.ip ∧ b.out = a.out ∧
      Fr a b irT) := by
  have hk := h.kc
  have hstkk : S.stk.length ≤ k := by have := h.stk.len; have := h.bsk; omega
  refine Hs.seqc (t1 := 3) (t2 := a.rc sSK + 6 * k + tc + 16) (gateP_spec n k S a h hW) (fun b hb => ?_) (by omega)
  obtain ⟨e1, r1, c1', i1, o1, f1⟩ := hb
  have k1 : KC b := hk.of_fr f1 (by decide)
  refine Hs.seqc (t1 := tc) (t2 := a.rc sSK + 5 * k + 12) (hcl b k1.z k1.one (by rw [r1, c1']; exact h.rccl) e1
    (fun y hy => f1 y (by simp [hy]))) (fun d hd => ?_) (by omega)
  obtain ⟨x2, f2⟩ := hd
  have hd : StkRel d S.stk := ⟨by rw [f2 iSp (by decide), f1 iSp (by decide)]; exact h.stk.sp,
    by rw [x2.ram sSK (by decide), r1]; exact h.stk.take, by rw [x2.ram sSK (by decide), r1]; exact h.stk.len⟩
  refine Hs.mono (nodeTail_spec n k S a d h hW S.stk x (fun y hy => hy) le_rfl (k1.of_fr f2 (by decide)) hd
    (by rw [x2.ram sSK (by decide), r1]) (by rw [x2.st, r1]) (by rw [x2.rc, c1'])
    (fun m h1 h2 => ⟨by rw [x2.ram m h2, r1], by rw [x2.rcs m h2, c1']⟩) (by rw [x2.ip, i1]) (by rw [x2.out, o1])
    ((Fr.weaken f1 (by simp [preT])).trans (Fr.weaken f2 (by simp [preT, clT]))))
    (by rw [x2.rcs sSK (by decide), c1']; omega) (fun b hb => hb)

def cstTokP : St VV MM := nulTokP clCstP
def inpTokP : St VV MM := nulTokP clInpP

theorem cstTokP_spec (n k : ℕ) (S : RS) (a : DS VV MM) (h : IR n k S a) (hW : 64 * (n + k) + 64 ≤ 2 ^ C.Wd)
    (b : Bool) (hp : a.env iPl = b.toNat)
    (hWc : ∀ c ∈ (rcl n S.idx (.cst b)).map Encodable.encode, c < 2 ^ C.Wd) :
    Hs C cstTokP a (a.rc sSK + 6 * k + 90) (fun d => IR n (k + 1) (S.step (.cst b)) d ∧
      (∀ m, m ≠ sSK → m ≠ sCL → d.ram m = a.ram m ∧ d.rc m = a.rc m) ∧ d.ip = a.ip ∧ d.out = a.out ∧
      Fr a d irT) :=
  nulTokP_spec clCstP 70 (.cst b) n k S a h hW (fun d hz _ hend hg hf =>
    clCstP_spec d n S.idx b hz hend hg (by rw [hf iPl (by decide), hp]) hWc)

theorem inpTokP_spec (n k : ℕ) (S : RS) (a : DS VV MM) (h : IR n k S a) (hW : 64 * (n + k) + 64 ≤ 2 ^ C.Wd)
    (j : ℕ) (hp : a.env iPl = j)
    (hWc : ∀ c ∈ (rcl n S.idx (.inp j)).map Encodable.encode, c < 2 ^ C.Wd) :
    Hs C inpTokP a (a.rc sSK + 6 * k + 161) (fun d => IR n (k + 1) (S.step (.inp j)) d ∧
      (∀ m, m ≠ sSK → m ≠ sCL → d.ram m = a.ram m ∧ d.rc m = a.rc m) ∧ d.ip = a.ip ∧ d.out = a.out ∧
      Fr a d irT) :=
  nulTokP_spec clInpP 141 (.inp j) n k S a h hW (fun d hz h1 hend hg hf =>
    clInpP_spec d n S.idx j hz h1 hend hg (by rw [hf iPl (by decide), hp]) hWc)

/-! ## Negation tokens -/

def unOpsP : St VV MM := .seq (.op (.add iX dN)) gateP

def negTokP : St VV MM := .seq (popP iX) (.seq unOpsP (.seq clNegP nodeEndP))

theorem negTokP_spec (n k : ℕ) (S : RS) (a : DS VV MM) (h : IR n k S a) (hW : 64 * (n + k) + 64 ≤ 2 ^ C.Wd)
    (hWc : ∀ c ∈ (rcl n S.idx (.neg (popS S.stk).1)).map Encodable.encode, c < 2 ^ C.Wd) :
    Hs C negTokP a (2 * a.rc sSK + 12 * k + 180) (fun d => IR n (k + 1) (S.step .neg) d ∧
      (∀ m, m ≠ sSK → m ≠ sCL → d.ram m = a.ram m ∧ d.rc m = a.rc m) ∧ d.ip = a.ip ∧ d.out = a.out ∧
      Fr a d irT) := by
  have hk := h.kc
  have hidx := h.bidx
  have hrsk : a.rc sSK ≤ k := le_trans h.rsk h.bsk
  have hstkk : S.stk.length ≤ k := by have := h.stk.len; have := h.bsk; omega
  set c := (popS S.stk).1 with hc
  set st1 := (popS S.stk).2 with hst1
  have hst1l : st1.length ≤ S.stk.length := popS_len _
  have hck : c ≤ k := popS_le _ _ h.vstk
  refine Hs.seqc (t1 := a.rc sSK + 5 * S.stk.length + 10) (t2 := a.rc sSK + 7 * k + 169)
    (popP_spec (C := C) iX (by decide) a S.stk h.stk hk.z hk.one (by omega)) (fun b1 hb1 => ?_) (by omega)
  obtain ⟨e1, s1, r1, q1, c1', i1, o1, f1⟩ := hb1
  rw [← hc] at e1; rw [← hst1] at s1
  have k1 : KC b1 := hk.of_fr f1 (by decide)
  have b1N : b1.env dN = n := by rw [f1 dN (by decide), h.dn]
  have b1I : b1.env iIdx = S.idx := by rw [f1 iIdx (by decide), h.idx]
  have s2 : Hs C unOpsP b1 5 (fun b2 => b2.env iX = n + c ∧ b2.env iG = n + S.idx ∧ b2.ram = b1.ram ∧
      b2.rc = b1.rc ∧ b2.ip = b1.ip ∧ b2.out = b1.out ∧ Fr b1 b2 [iX, iG]) := by
    apply hs_of_wpc
    simp only [unOpsP, gateP, wpc, opwp]
    vsimp [e1, b1N, b1I]
    and_split
    all_goals first | omega | rfl | fr_tac | skip
  refine Hs.seqc (t1 := 5) (t2 := a.rc sSK + 7 * k + 163) s2 (fun b2 hb2 => ?_) (by omega)
  obtain ⟨e2X, e2G, r2, c2', i2, o2, f2⟩ := hb2
  have k2 : KC b2 := k1.of_fr f2 (by decide)
  have hcl2 : b2.rc sCL = (b2.ram sCL).length := by
    rw [c2', r2, c1' sCL (by decide), r1]; exact h.rccl
  refine Hs.seqc (t1 := 141) (t2 := a.rc sSK + 7 * k + 21) (clNegP_spec b2 n S.idx c k2.z k2.one hcl2 e2G e2X hWc)
    (fun b3 hb3 => ?_) (by omega)
  obtain ⟨x3, f3⟩ := hb3
  have s3 : StkRel b3 st1 := ⟨by rw [f3 iSp (by decide), f2 iSp (by decide)]; exact s1.sp,
    by rw [x3.ram sSK (by decide), r2]; exact s1.take, by rw [x3.ram sSK (by decide), r2]; exact s1.len⟩
  have hq3 : b3.rc sSK ≤ a.rc sSK + k := by rw [x3.rcs sSK (by decide), c2']; omega
  refine Hs.mono (nodeTail_spec n k S a b3 h hW st1 (.neg c) (fun y hy => popS_mem _ _ hy) (popS_len _)
    (k2.of_fr f3 (by decide)) s3 (by rw [x3.ram sSK (by decide), r2, r1]) (by rw [x3.st, r2, r1])
    (by rw [x3.rc, c2', c1' sCL (by decide)])
    (fun m h1 h2 => ⟨by rw [x3.ram m h2, r2, r1], by rw [x3.rcs m h2, c2', c1' m h1]⟩) (by rw [x3.ip, i2, i1])
    (by rw [x3.out, o2, o1])
    ((Fr.weaken f1 (by simp [preT])).trans ((Fr.weaken f2 (by simp [preT])).trans (Fr.weaken f3 (by simp [preT, clT])))))
    (by omega) (fun b hb => hb)

end NearCubicGates.Adapters.Compile
