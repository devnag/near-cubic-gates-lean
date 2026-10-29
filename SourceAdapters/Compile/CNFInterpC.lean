import SourceAdapters.Compile.CNFInterpB

/-!
# Token interpreter, part C: the interpreter relation and the binary node tokens

`IR n k S a`: the cell state `a` represents the token-machine state `S` (`CNFRpn.RS`) over `n` circuit inputs; the
clause store holds exactly the codes of `circuitInputTautologies n ++ rclFrom n 0 S.nodes` (proof of `lem:multitape-refuter`), and `k`
bounds every store length and stored value (for the cost and width bounds). `binTokP` (conjunction/disjunction)
realizes `RS.step` on `.conj`/`.disj` (`conjTokP_spec`, `disjTokP_spec`).
-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells NearCubicWires.TseitinCNF NearCubicWires.CircuitInputCNF
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- The interpreter relation. -/
structure IR (n k : ℕ) (S : RS) (a : DS VV MM) : Prop where
  kc : KC a
  dn : a.env dN = n
  idx : a.env iIdx = S.idx
  nodes : S.nodes.length = S.idx
  stk : StkRel a S.stk
  wl : a.env iWl = S.wires.length
  wires : (a.ram sWM).take S.wires.length = S.wires
  wlen : S.wires.length ≤ (a.ram sWM).length
  nc : a.env iNc = S.next.length
  next : (a.ram sNW).take S.next.length = S.next
  nlen : S.next.length ≤ (a.ram sNW).length
  rcnw : a.rc sNW = S.next.length
  cl : a.ram sCL = (circuitInputTautologies n ++ rclFrom n 0 S.nodes).map Encodable.encode
  rccl : a.rc sCL = (a.ram sCL).length
  bsk : (a.ram sSK).length ≤ k
  rsk : a.rc sSK ≤ (a.ram sSK).length
  bwm : (a.ram sWM).length ≤ k
  rwm : a.rc sWM ≤ (a.ram sWM).length
  bnw : (a.ram sNW).length ≤ k
  bidx : S.idx ≤ k
  vstk : ∀ x ∈ S.stk, x ≤ k
  vwires : ∀ x ∈ S.wires, x ≤ k
  vnext : ∀ x ∈ S.next, x ≤ k

/-- The registers the interpreter may change. -/
def irT : List (Fin VV) := [iIdx, iSp, iWl, iNc, iTk, iPl, iK, iX, iY, iG, iS, iJ, c0, c1, c2, c3, c4, c5, c6]

variable {C : Ctx}

theorem popS_mem (st : List ℕ) (x : ℕ) (hx : x ∈ (popS st).2) : x ∈ st := by
  cases st with
  | nil => simp [popS] at hx
  | cons t r => simp [popS] at hx; exact List.mem_cons_of_mem _ hx

theorem popS_le (st : List ℕ) (k : ℕ) (h : ∀ x ∈ st, x ≤ k) : (popS st).1 ≤ k := by
  cases st with
  | nil => simp [popS]
  | cons t r => exact h t (by simp)

theorem popS_len (st : List ℕ) : (popS st).2.length ≤ st.length := by
  cases st <;> simp [popS]

/-- The gate variable `iG := n + idx`, operands `iX += n`, `iY += n`. -/
def binOpsP : St VV MM := .seq (.op (.add iX dN)) (.seq (.op (.add iY dN)) (.seq (.op (.copy iG dN)) (.op (.add iG iIdx))))

/-- Push the node index and increment it. -/
def nodeEndP : St VV MM := .seq (pushP iIdx) (.op (.inc iIdx))

/-- A binary node token: pop the right operand into `iY`, the left into `iX`, emit the clauses, push the index. -/
def binTokP (cl : St VV MM) : St VV MM := .seq (popP iY) (.seq (popP iX) (.seq binOpsP (.seq cl nodeEndP)))

/-- The common part of the binary node tokens. -/
theorem binTokP_spec (cl : St VV MM) (tc : ℕ) (mk : ℕ → ℕ → RNode) (n k : ℕ) (S : RS) (a : DS VV MM)
    (h : IR n k S a) (hW : 64 * (n + k) + 64 ≤ 2 ^ C.Wd)
    (hcl : ∀ (b : DS VV MM), b.env vZ = 0 → b.env v1 = 1 → b.rc sCL = (b.ram sCL).length →
      b.env iG = n + S.idx → b.env iX = n + (popS (popS S.stk).2).1 → b.env iY = n + (popS S.stk).1 →
      Hs C cl b tc (fun d => ExtS sCL b d ((rcl n S.idx (mk (popS (popS S.stk).2).1 (popS S.stk).1)).map
        Encodable.encode) ∧ Fr b d clT)) :
    Hs C (binTokP cl) a (3 * a.rc sSK + 20 * k + tc + 60) (fun b =>
      IR n (k + 1) (S.push (popS (popS S.stk).2).2 (mk (popS (popS S.stk).2).1 (popS S.stk).1)) b ∧
      (∀ m, m ≠ sSK → m ≠ sCL → b.ram m = a.ram m ∧ b.rc m = a.rc m) ∧ b.ip = a.ip ∧ b.out = a.out ∧
      Fr a b irT) := by
  have hk := h.kc
  set r := (popS S.stk).1 with hr
  set st1 := (popS S.stk).2 with hst1
  set l := (popS st1).1 with hl
  set st2 := (popS st1).2 with hst2
  have hlen1 : st1.length ≤ S.stk.length := popS_len _
  have hlen2 : st2.length ≤ st1.length := popS_len _
  have hstkk : S.stk.length ≤ k := by have := h.stk.len; have := h.bsk; omega
  have hrk : r ≤ k := popS_le _ _ h.vstk
  have hlk : l ≤ k := popS_le _ _ (fun x hx => h.vstk x (popS_mem _ _ hx))
  -- pop r
  have hrsk : a.rc sSK ≤ k := le_trans h.rsk h.bsk
  have hidx := h.bidx
  refine Hs.seqc (t1 := a.rc sSK + 5 * S.stk.length + 10) (t2 := 2 * a.rc sSK + 15 * k + tc + 49)
    (popP_spec (C := C) iY (by decide) a S.stk h.stk hk.z hk.one (by omega)) (fun b1 hb1 => ?_) (by omega)
  obtain ⟨e1, s1, r1, q1, c1', i1, o1, f1⟩ := hb1
  rw [← hr] at e1; rw [← hst1] at s1
  have k1 : KC b1 := hk.of_fr f1 (by decide)
  -- pop l
  refine Hs.seqc (t1 := b1.rc sSK + 5 * st1.length + 10) (t2 := a.rc sSK + 9 * k + tc + 38)
    (popP_spec (C := C) iX (by decide) b1 st1 s1 k1.z k1.one (by omega)) (fun b2 hb2 => ?_)
    (by omega)
  obtain ⟨e2, s2, r2, q2, c2', i2, o2, f2⟩ := hb2
  rw [← hl] at e2; rw [← hst2] at s2
  have k2 : KC b2 := k1.of_fr f2 (by decide)
  have fb2 : ∀ y, y ∉ [iS, iJ, iSp, iY, iX] → b2.env y = a.env y := fun y hy => by
    rw [f2 y (by simp at hy ⊢; tauto), f1 y (by simp at hy ⊢; tauto)]
  have b2Y : b2.env iY = r := by rw [f2 iY (by decide), e1]
  -- gate and operand variables
  have s3 : Hs C binOpsP b2 7 (fun b3 => b3.env iX = n + l ∧ b3.env iY = n + r ∧ b3.env iG = n + S.idx ∧
      b3.ram = b2.ram ∧ b3.rc = b2.rc ∧ b3.ip = b2.ip ∧ b3.out = b2.out ∧ Fr b2 b3 [iX, iY, iG]) := by
    apply hs_of_wpc
    simp only [binOpsP, wpc, opwp]
    vsimp [e2, b2Y, fb2 dN (by decide), fb2 iIdx (by decide), h.dn, h.idx]
    and_split
    all_goals first | omega | rfl | fr_tac | skip
  refine Hs.seqc (t1 := 7) (t2 := a.rc sSK + 9 * k + tc + 30) s3 (fun b3 hb3 => ?_) (by omega)
  obtain ⟨e3X, e3Y, e3G, r3, c3', i3, o3, f3⟩ := hb3
  have k3 : KC b3 := k2.of_fr f3 (by decide)
  have hcl3 : b3.rc sCL = (b3.ram sCL).length := by
    rw [c3', r3, c2' sCL (by decide), r2, c1' sCL (by decide), r1]; exact h.rccl
  -- clauses
  refine Hs.seqc (t1 := tc) (t2 := a.rc sSK + 9 * k + 29) (hcl b3 k3.z k3.one hcl3 e3G e3X e3Y)
    (fun b4 hb4 => ?_) (by omega)
  obtain ⟨x4, f4⟩ := hb4
  have k4 : KC b4 := k3.of_fr f4 (by decide)
  have b4idx : b4.env iIdx = S.idx := by
    rw [f4 iIdx (by decide), f3 iIdx (by decide), fb2 iIdx (by decide), h.idx]
  have b4sp : StkRel b4 st2 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [f4 iSp (by decide), f3 iSp (by decide)]; exact s2.sp
    · rw [x4.ram sSK (by decide), r3]; exact s2.take
    · rw [x4.ram sSK (by decide), r3]; exact s2.len
  have b4rcsk : b4.rc sSK ≤ a.rc sSK + k := by
    rw [x4.rcs sSK (by decide), c3']; omega
  -- push the index and increment
  refine Hs.seqc (t1 := b4.rc sSK + 5 * st2.length + 10) (t2 := 1) (pushP_spec (C := C) iIdx (by decide) b4 st2
    b4sp (by omega)) (fun b5 hb5 => ?_) (by omega)
  obtain ⟨s5, l5, c5', u5, i5, o5, f5⟩ := hb5
  rw [b4idx] at s5
  have b5idx : b5.env iIdx = S.idx := by rw [f5 iIdx (by decide), b4idx]
  refine Hs.op (OpEx.inc iIdx b5 (by rw [b5idx]; omega)) ?_
  have hram : ∀ m, m ≠ sSK → m ≠ sCL → b5.ram m = a.ram m := fun m h1 h2 => by
    rw [(u5 m h1).1, x4.ram m h2, r3, r2, r1]
  have hrc : ∀ m, m ≠ sSK → m ≠ sCL → b5.rc m = a.rc m := fun m h1 h2 => by
    rw [(u5 m h1).2, x4.rcs m h2, c3', c2' m h1, c1' m h1]
  have hfr5 : ∀ y, y ∉ irT → b5.env y = a.env y := fun y hy => by
    simp only [irT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [f5 y (by simp [hy.2.2.2.2.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.2.2.2.2.1, hy.2.1]),
      f4 y (by simp [clT]; tauto), f3 y (by simp; tauto), fb2 y (by simp; tauto)]
  have hS := h.nodes
  have fa : ∀ y, y ∉ [iS, iJ, iSp, iY, iX, iG, iIdx] → y ∉ clT → b5.env y = a.env y := fun y hy hc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [f5 y (by simp [hy.1, hy.2.1, hy.2.2.1]), f4 y hc, f3 y (by simp [hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2.1]),
      fb2 y (by simp [hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1])]
  have k5 : KC b5 := k4.of_fr f5 (by decide)
  have hSK4 : b4.ram sSK = a.ram sSK := by rw [x4.ram sSK (by decide), r3, r2, r1]
  have hCL5 : b5.ram sCL = b4.ram sCL := (u5 sCL (by decide)).1
  have hCLr5 : b5.rc sCL = b4.rc sCL := (u5 sCL (by decide)).2
  have hram : ∀ m, m ≠ sSK → m ≠ sCL → b5.ram m = a.ram m := fun m h1 h2 => by
    rw [(u5 m h1).1, x4.ram m h2, r3, r2, r1]
  have hrc : ∀ m, m ≠ sSK → m ≠ sCL → b5.rc m = a.rc m := fun m h1 h2 => by
    rw [(u5 m h1).2, x4.rcs m h2, c3', c2' m h1, c1' m h1]
  have hnodes : (circuitInputTautologies n ++ rclFrom n 0 (S.nodes ++ [mk l r])).map Encodable.encode =
      (circuitInputTautologies n ++ rclFrom n 0 S.nodes).map Encodable.encode ++
        (rcl n S.idx (mk l r)).map Encodable.encode := by
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
  · simp only [DS.set_ram, RS.push]; rw [hCL5, x4.st, r3, r2, r1, h.cl, hnodes]
  · simp only [DS.set_ram, DS.set_rc]; rw [hCL5, hCLr5, x4.st, x4.rc, hcl3]; simp
  · simp only [DS.set_ram]; have := s5.len; rw [hSK4] at l5; have := h.bsk; simp at this ⊢; omega
  · simp only [DS.set_ram, DS.set_rc]; rw [c5']; have := s5.len; simp at this ⊢; omega
  · simp only [DS.set_ram]; rw [hram sWM (by decide) (by decide)]; have := h.bwm; omega
  · simp only [DS.set_ram, DS.set_rc]; rw [hram sWM (by decide) (by decide), hrc sWM (by decide) (by decide)]
    exact h.rwm
  · simp only [DS.set_ram]; rw [hram sNW (by decide) (by decide)]; have := h.bnw; omega
  · simp only [RS.push]; have := h.bidx; omega
  · intro x hx
    simp only [RS.push, List.mem_cons] at hx
    rcases hx with hx | hx
    · have := h.bidx; omega
    · have := h.vstk x (popS_mem _ _ (popS_mem _ _ hx)); omega
  · intro x hx; have := h.vwires x hx; omega
  · intro x hx; have := h.vnext x hx; omega
  · intro m h1 h2; exact ⟨by simp [hram m h1 h2], by simp [hrc m h1 h2]⟩
  · simp only [DS.set_ip]; rw [i5, x4.ip, i3, i2, i1]
  · simp only [DS.set_out]; rw [o5, x4.out, o3, o2, o1]
  · intro y hy
    simp only [irT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [DS.set_env_ne _ _ hy.1]
    exact fa y (by simp; tauto) (by simp [clT]; tauto)

def conjTokP : St VV MM := binTokP clConjP
def disjTokP : St VV MM := binTokP clDisjP

theorem conjTokP_spec (n k : ℕ) (S : RS) (a : DS VV MM) (h : IR n k S a) (hW : 64 * (n + k) + 64 ≤ 2 ^ C.Wd)
    (hWc : ∀ c ∈ (rcl n S.idx (.conj (popS (popS S.stk).2).1 (popS S.stk).1)).map Encodable.encode, c < 2 ^ C.Wd) :
    Hs C conjTokP a (3 * a.rc sSK + 20 * k + 272) (fun b => IR n (k + 1) (S.step .conj) b ∧
      (∀ m, m ≠ sSK → m ≠ sCL → b.ram m = a.ram m ∧ b.rc m = a.rc m) ∧ b.ip = a.ip ∧ b.out = a.out ∧
      Fr a b irT) :=
  binTokP_spec clConjP 212 RNode.conj n k S a h hW
    (fun b hz h1 hend hg hx hy => clConjP_spec b n S.idx _ _ hz h1 hend hg hx hy hWc)

theorem disjTokP_spec (n k : ℕ) (S : RS) (a : DS VV MM) (h : IR n k S a) (hW : 64 * (n + k) + 64 ≤ 2 ^ C.Wd)
    (hWc : ∀ c ∈ (rcl n S.idx (.disj (popS (popS S.stk).2).1 (popS S.stk).1)).map Encodable.encode, c < 2 ^ C.Wd) :
    Hs C disjTokP a (3 * a.rc sSK + 20 * k + 272) (fun b => IR n (k + 1) (S.step .disj) b ∧
      (∀ m, m ≠ sSK → m ≠ sCL → b.ram m = a.ram m ∧ b.rc m = a.rc m) ∧ b.ip = a.ip ∧ b.out = a.out ∧
      Fr a b irT) :=
  binTokP_spec clDisjP 212 RNode.disj n k S a h hW
    (fun b hz h1 hend hg hx hy => clDisjP_spec b n S.idx _ _ hz h1 hend hg hx hy hWc)

end NearCubicGates.Adapters.Compile
