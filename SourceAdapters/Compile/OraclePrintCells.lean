import Proof.Gates.Cells.Kit
import SourceAdapters.Compile.OraclePrintBounds

/-!
# Cell-language emitters for the native word of an oracle circuit

 (`thm:short-pcp-ours`, Step 4): the algorithm \(A\) "computes [...] \(C^O_x\) in
\(\poly(n,\log T)\) time"; (`cor:short-pcp-clock`) charges the same construction. The written object
is the native word `OracleOutput.word` (`Statement.lean:1500`): `natWord ℓ ++ natWord |nodes| ++ node words ++
natWord output`, where a node word (`oracleNodeWord`, `Statement.lean:1484`) is the tag `0…4` followed by two
`natWord` fields (`0` when unused) for a Boolean node, and the tag `5` followed by exactly `ℓ` argument wires for an
oracle gate. This module gives actual cell-language programs printing each piece, with exact output, cost, and
footprint, for the printing program of `OraclePrintAssembly.OracleProgramRuns`.

Footprint (all specs): scratch registers `nodeScratch = [t3, t5, t6, t7, t8, t9, argCount]` (`argCount` is
register 100); operand registers are parameters outside `nodeScratch`; the argument wires of an oracle gate are read
from a record store `m` (a parameter) starting at its cursor, which advances by exactly `ℓ`; every other store,
cursor, the input position and the call channels are unchanged; the constants `vZ v1 v2` are preserved.

-/

namespace NearCubicGates.Adapters.Compile.OraclePrint

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.Bindings.MW20
open NearCubicGates.Close.Cells

set_option autoImplicit false

/-! ## The fields of a node -/

/-- The tag field: `0` constant, `1` input, `2` NOT, `3` AND, `4` OR, `5` oracle gate. -/
def nodeTag {n arity : ℕ} : OracleNode n arity → ℕ
  | .const _ => 0
  | .input _ => 1
  | .not _ => 2
  | .and _ _ => 3
  | .or _ _ => 4
  | .oracle _ => 5

/-- The first numeric field of a Boolean node (`0` for an oracle gate, where it is not printed). -/
def nodeLeft {n arity : ℕ} : OracleNode n arity → ℕ
  | .const value => value.toNat
  | .input index => index.val
  | .not child => child
  | .and left _ => left
  | .or left _ => left
  | .oracle _ => 0

/-- The second numeric field of a Boolean node (`0` when unused). -/
def nodeRight {n arity : ℕ} : OracleNode n arity → ℕ
  | .and _ right => right
  | .or _ right => right
  | _ => 0

/-- The argument wires of an oracle gate (empty for a Boolean node). -/
def nodeArgs {n arity : ℕ} : OracleNode n arity → List ℕ
  | .oracle args => List.ofFn args
  | _ => []

theorem nodeTag_le {n arity : ℕ} (nd : OracleNode n arity) : nodeTag nd ≤ 5 := by
  cases nd <;> simp [nodeTag]

theorem nodeArgs_of_ne {n arity : ℕ} (nd : OracleNode n arity) (h : nodeTag nd ≠ 5) : nodeArgs nd = [] := by
  cases nd <;> simp_all [nodeTag, nodeArgs]

theorem nodeArgs_length_le {n arity : ℕ} (nd : OracleNode n arity) : (nodeArgs nd).length ≤ arity := by
  cases nd <;> simp [nodeArgs]

theorem nodeArgs_length_of_eq {n arity : ℕ} (nd : OracleNode n arity) (h : nodeTag nd = 5) :
    (nodeArgs nd).length = arity := by
  cases nd <;> simp_all [nodeTag, nodeArgs]

/-- **The node word from its fields** (`Statement.lean:1484`): the tag, then either the two numeric fields or the
argument wires. -/
theorem oracleNodeWord_fields {n arity : ℕ} (nd : OracleNode n arity) :
    oracleNodeWord nd = natWord (nodeTag nd) ++
      (if nodeTag nd = 5 then (nodeArgs nd).flatMap natWord else natWord (nodeLeft nd) ++ natWord (nodeRight nd)) := by
  cases nd with
  | const value => simp [oracleNodeWord, nodeTag, nodeLeft, nodeRight]
  | input index => simp [oracleNodeWord, nodeTag, nodeLeft, nodeRight]
  | not child => simp [oracleNodeWord, nodeTag, nodeLeft, nodeRight]
  | and left right => simp [oracleNodeWord, nodeTag, nodeLeft, nodeRight]
  | or left right => simp [oracleNodeWord, nodeTag, nodeLeft, nodeRight]
  | oracle args =>
    simp only [oracleNodeWord, nodeTag, nodeArgs, if_true]
    congr 1
    simp [List.flatMap_def, List.map_ofFn, Function.comp_def]

/-- Every printed field has at most `B` bits. -/
def FieldsBound {n arity : ℕ} (nd : OracleNode n arity) (B : ℕ) : Prop :=
  natBitLength (nodeTag nd) ≤ B ∧ natBitLength (nodeLeft nd) ≤ B ∧ natBitLength (nodeRight nd) ≤ B ∧
    ∀ v ∈ nodeArgs nd, natBitLength v ≤ B

theorem natBitLength_mono {x y : ℕ} (h : x ≤ y) : natBitLength x ≤ natBitLength y := by
  unfold natBitLength; exact Nat.add_le_add_right (Nat.log_mono_right h) 1

/-- Every field of a node well formed at position `idx` is at most `idx + n + 5`. -/
theorem fieldsBound_of_wellFormed {n arity : ℕ} (nd : OracleNode n arity) (idx : ℕ) (h : nd.WellFormedAt idx) :
    FieldsBound nd (natBitLength (idx + n + 5)) := by
  have hle : ∀ x, x ≤ idx + n + 5 → natBitLength x ≤ natBitLength (idx + n + 5) := fun _ hx => natBitLength_mono hx
  refine ⟨hle _ (by have := nodeTag_le nd; omega), hle _ ?_, hle _ ?_, fun v hv => hle _ ?_⟩
  · cases nd with
    | const value => have := Bool.toNat_le value; simp [nodeLeft]; omega
    | input index => have := index.isLt; simp [nodeLeft]; omega
    | not child => simp only [OracleNode.WellFormedAt] at h; simp [nodeLeft]; omega
    | and left right => simp only [OracleNode.WellFormedAt] at h; simp [nodeLeft]; omega
    | or left right => simp only [OracleNode.WellFormedAt] at h; simp [nodeLeft]; omega
    | oracle args => simp [nodeLeft]
  · cases nd with
    | and left right => simp only [OracleNode.WellFormedAt] at h; simp [nodeRight]; omega
    | or left right => simp only [OracleNode.WellFormedAt] at h; simp [nodeRight]; omega
    | _ => simp [nodeRight]
  · cases nd with
    | oracle args =>
      simp only [nodeArgs, List.mem_ofFn] at hv
      obtain ⟨j, rfl⟩ := hv
      simp only [OracleNode.WellFormedAt] at h
      have := h j; omega
    | _ => simp [nodeArgs] at hv

/-- Every node of a circuit with arity `ℓ` and `ℓ` inputs has fields of at most `natBitLength (ℓ + |C| + 5)` bits. -/
theorem fieldsBound_of_circuit {ell : ℕ} (C : OracleCircuit ell ell) (k : ℕ) (hk : k < C.nodes.length) :
    FieldsBound C.nodes[k] (natBitLength (ell + C.size + 5)) := by
  have hw := C.wellFormed ⟨k, hk⟩
  have hb := fieldsBound_of_wellFormed (C.nodes.get ⟨k, hk⟩) k hw
  have hm : natBitLength (k + ell + 5) ≤ natBitLength (ell + C.size + 5) := by
    apply natBitLength_mono; change k < C.nodes.length at hk; change k + ell + 5 ≤ ell + C.nodes.length + 5; omega
  obtain ⟨h1, h2, h3, h4⟩ := hb
  exact ⟨h1.trans hm, h2.trans hm, h3.trans hm, fun v hv => (h4 v hv).trans hm⟩

/-! ## The streamed word -/

/-- The printed word after the header and the first `k` nodes. -/
def streamWord {ell : ℕ} (C : OracleCircuit ell ell) (k : ℕ) : List Bool :=
  natWord ell ++ natWord C.nodes.length ++ (C.nodes.take k).flatMap oracleNodeWord

theorem streamWord_zero {ell : ℕ} (C : OracleCircuit ell ell) :
    streamWord C 0 = natWord ell ++ natWord C.nodes.length := by
  simp [streamWord]

theorem streamWord_succ {ell : ℕ} (C : OracleCircuit ell ell) (k : ℕ) (hk : k < C.nodes.length) :
    streamWord C (k + 1) = streamWord C k ++ oracleNodeWord C.nodes[k] := by
  unfold streamWord
  rw [List.take_succ_eq_append_getElem hk, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

/-- The whole native word: every node streamed, then the output address. -/
theorem word_eq_stream {ell : ℕ} (C : OracleCircuit ell ell) :
    OracleOutput.word ⟨ell, C⟩ = streamWord C C.nodes.length ++ natWord C.output.val := by
  simp [OracleOutput.word, streamWord]

/-! ## Footprint -/

/-- The loop counter of the argument loop (also holds the tag constant `5`). -/
def argCount : Fin VV := ⟨100, by decide⟩

/-- The scratch registers of the field emitter: `t3` and the scratch of `emitNatO`. -/
def fieldScratch : List (Fin VV) := [t3, t5, t6, t7, t8, t9]

/-- The scratch registers of the node emitter. -/
def nodeScratch : List (Fin VV) := [t3, t5, t6, t7, t8, t9, argCount]

theorem DS.set_set (a : DS VV MM) (x : Fin VV) (v w : ℕ) : (a.set x v).set x w = a.set x w := by
  simp [DS.set]

/-! ## One field -/

/-- Print `natWord (x)`. -/
def emitField (x : Fin VV) : St VV MM := .seq (.op (.copy t3 x)) emitNatO

variable {C : Ctx}

theorem emitField_spec (x : Fin VV) (hx : x ≠ t3) (a : DS VV MM) (hc : Cst a) (hW : 2 ≤ C.Wd)
    (hv : natBitLength (a.env x) + 2 < 2 ^ C.Wd) :
    Hs C (emitField x) a (40 * natBitLength (a.env x) + 42) (fun b => b.out = a.out ++ natWord (a.env x) ∧
      b.ip = a.ip ∧ b.ram = a.ram ∧ b.rc = a.rc ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Cst b ∧
      Fr a b fieldScratch) := by
  refine Hs.mono (t := 1 + (40 * natBitLength (a.env x) + 40) + 1) ?_ (by omega) (fun b hb => hb)
  refine Hs.seq (hs_copy C t3 x a (Ne.symm hx)) (fun d hd => ?_)
  subst hd
  have hc' : Cst (a.set t3 (a.env x)) := Cst.of_fr hc (Fr.set a (a.env x) (T := [t3]) (by simp)) (by decide)
  have e := emitNatO_spec (C := C) (a.set t3 (a.env x)) hc' hW (by rw [DS.set_env_self]; exact hv)
  rw [DS.set_env_self] at e
  refine Hs.mono e le_rfl ?_
  rintro b ⟨h1, h2, h3, h4⟩
  simp only [Prod.mk.injEq] at h2
  obtain ⟨hip, hram, hrc, hkin, hkout, hkc⟩ := h2
  refine ⟨h1, hip, hram, hrc, hkin, hkout, hkc, h3, fun y hy => ?_⟩
  have hy' : y ∉ emitNatT := fun h => hy (by simp [emitNatT, fieldScratch] at h ⊢; tauto)
  have hyt : y ≠ t3 := fun h => hy (by simp [fieldScratch, h])
  rw [h4 y hy', DS.set_env_ne _ _ hyt]

/-! ## Two fields: the header, and the two numeric fields of a Boolean node -/

/-- Print `natWord (x) ++ natWord (y)`. -/
def emitPair (x y : Fin VV) : St VV MM := .seq (emitField x) (emitField y)

theorem emitPair_spec (x y : Fin VV) (hx : x ∉ fieldScratch) (hy : y ∉ fieldScratch)
    (a : DS VV MM) (hc : Cst a) (hW : 2 ≤ C.Wd) (B : ℕ) (hBW : B + 2 < 2 ^ C.Wd)
    (h1 : natBitLength (a.env x) ≤ B) (h2 : natBitLength (a.env y) ≤ B) :
    Hs C (emitPair x y) a (80 * B + 85) (fun b =>
      b.out = a.out ++ natWord (a.env x) ++ natWord (a.env y) ∧
      b.ip = a.ip ∧ b.ram = a.ram ∧ b.rc = a.rc ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Cst b ∧
      Fr a b fieldScratch) := by
  have hxt : x ≠ t3 := fun h => hx (by simp [fieldScratch, h])
  have hyt : y ≠ t3 := fun h => hy (by simp [fieldScratch, h])
  refine Hs.mono (t := (40 * B + 42) + (40 * B + 42) + 1) ?_ (by omega) (fun b hb => hb)
  refine Hs.seq (Hs.mono (emitField_spec x hxt a hc hW (by omega)) (t' := 40 * B + 42) (by omega)
    (fun b hb => hb)) (fun d hd => ?_)
  obtain ⟨o1, i1, r1, c1, k1, k2, k3, cs1, f1⟩ := hd
  have hd' : d.env y = a.env y := f1 y hy
  refine Hs.mono (emitField_spec y hyt d cs1 hW (by rw [hd']; omega)) (t' := 40 * B + 42)
    (by rw [hd']; omega) ?_
  rintro b ⟨o2, i2, r2, c2, k4, k5, k6, cs2, f2⟩
  refine ⟨by rw [o2, o1, hd'], i2.trans i1, r2.trans r1, c2.trans c1, k4.trans k1, k5.trans k2, k6.trans k3, cs2,
    Fr.trans f1 f2⟩

/-- Print the header `natWord ℓ ++ natWord |nodes|` of `OracleOutput.word` from two registers. -/
def emitHeader (ellR countR : Fin VV) : St VV MM := emitPair ellR countR

theorem emitHeader_spec {ell : ℕ} (C0 : OracleCircuit ell ell) (ellR countR : Fin VV) (hE : ellR ∉ fieldScratch)
    (hN : countR ∉ fieldScratch) (a : DS VV MM) (hc : Cst a) (hW : 2 ≤ C.Wd) (B : ℕ) (hBW : B + 2 < 2 ^ C.Wd)
    (hell : a.env ellR = ell) (hcount : a.env countR = C0.nodes.length)
    (h1 : natBitLength ell ≤ B) (h2 : natBitLength C0.nodes.length ≤ B) :
    Hs C (emitHeader ellR countR) a (80 * B + 85) (fun b => b.out = a.out ++ streamWord C0 0 ∧
      b.ip = a.ip ∧ b.ram = a.ram ∧ b.rc = a.rc ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Cst b ∧
      Fr a b fieldScratch) := by
  refine Hs.mono (emitPair_spec ellR countR hE hN a hc hW B hBW (by rw [hell]; exact h1)
    (by rw [hcount]; exact h2)) le_rfl ?_
  rintro b ⟨o, rest⟩
  exact ⟨by rw [o, hell, hcount, streamWord_zero, List.append_assoc], rest⟩

/-- Print the output address `natWord (outR)`, the last field of `OracleOutput.word`. -/
def emitTrailer (outR : Fin VV) : St VV MM := emitField outR

theorem emitTrailer_spec {ell : ℕ} (C0 : OracleCircuit ell ell) (outR : Fin VV) (hO : outR ∉ fieldScratch)
    (a : DS VV MM) (hc : Cst a) (hW : 2 ≤ C.Wd) (B : ℕ) (hBW : B + 2 < 2 ^ C.Wd)
    (hout : a.env outR = C0.output.val) (h1 : natBitLength C0.output.val ≤ B)
    (hstream : a.out = streamWord C0 C0.nodes.length) :
    Hs C (emitTrailer outR) a (40 * B + 42) (fun b => b.out = OracleOutput.word ⟨ell, C0⟩ ∧
      b.ip = a.ip ∧ b.ram = a.ram ∧ b.rc = a.rc ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Cst b ∧
      Fr a b fieldScratch) := by
  have hOt : outR ≠ t3 := fun h => hO (by simp [fieldScratch, h])
  refine Hs.mono (emitField_spec outR hOt a hc hW (by rw [hout]; omega)) (by rw [hout]; omega) ?_
  rintro b ⟨o, rest⟩
  exact ⟨by rw [o, hstream, hout, word_eq_stream], rest⟩

/-! ## The argument wires of an oracle gate -/

theorem scratch_facts {y : Fin VV} (hy : y ∉ nodeScratch) :
    y ≠ t3 ∧ y ∉ emitNatT ∧ y ≠ argCount ∧ y ∉ fieldScratch := by
  simp only [nodeScratch, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  obtain ⟨h3, h5, h6, h7, h8, h9, hA⟩ := hy
  refine ⟨h3, ?_, hA, ?_⟩
  · simp only [emitNatT, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨h5, h6, h7, h8, h9⟩
  · simp only [fieldScratch, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨h3, h5, h6, h7, h8, h9⟩

theorem fieldScratch_sub (y : Fin VV) (hy : y ∈ fieldScratch) : y ∈ nodeScratch := by
  simp only [fieldScratch, nodeScratch, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
  tauto

/-- One pass: read the next argument wire from store `m`, print it, count it. -/
def argBody (m : Fin MM) : St VV MM := .seq (.op (.rdM m t3)) (.seq emitNatO (.op (.inc argCount)))

/-- Print the argument wires stored in `m` from its cursor; their number is in register `ellR`. -/
def emitArgs (ellR : Fin VV) (m : Fin MM) : St VV MM :=
  .seq (.op (.zero argCount)) (.loop (.lt argCount ellR) (argBody m))

theorem emitArgs_spec (ellR : Fin VV) (hE : ellR ∉ nodeScratch) (m : Fin MM) (args rest : List ℕ) (B : ℕ)
    (a : DS VV MM) (hc : Cst a) (hW : 2 ≤ C.Wd) (hell : a.env ellR = args.length)
    (hlen : args.length < 2 ^ C.Wd) (hmem : (a.ram m).drop (a.rc m) = args ++ rest)
    (hB : ∀ v ∈ args, natBitLength v ≤ B) (hBW : B + 2 < 2 ^ C.Wd) :
    Hs C (emitArgs ellR m) a (args.length * (40 * B + 46) + 4) (fun b =>
      b.out = a.out ++ args.flatMap natWord ∧ b.ip = a.ip ∧ b.ram = a.ram ∧
      b.rc = Function.update a.rc m (a.rc m + args.length) ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
      Cst b ∧ Fr a b nodeScratch) := by
  have hEc : argCount ≠ ellR := fun h => hE (by simp [nodeScratch, h])
  have hlenm : ∀ k < args.length, a.rc m + k < (a.ram m).length := by
    intro k hk
    have := congrArg List.length hmem
    simp only [List.length_drop, List.length_append] at this
    omega
  have hget : ∀ k (hk : k < args.length), (a.ram m).getD (a.rc m + k) 0 = args[k] := by
    intro k hk
    have h1 : (a.ram m).getD (a.rc m + k) 0 = ((a.ram m).drop (a.rc m)).getD k 0 := by
      simp [List.getD_eq_getElem?_getD]
    rw [h1, hmem, List.getD_append _ _ _ _ hk]
    simp [List.getD_eq_getElem?_getD, hk]
  let I : ℕ → DS VV MM → Prop := fun k b => b.env argCount = k ∧
    b.out = a.out ++ (args.take k).flatMap natWord ∧ b.ip = a.ip ∧ b.ram = a.ram ∧
    b.rc = Function.update a.rc m (a.rc m + k) ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
    Fr a b nodeScratch
  have hloop : ∀ b, I 0 b → Hs C (.loop (.lt argCount ellR) (argBody m)) b
      (args.length * ((40 * B + 44) + 2) + 2) (I args.length) := by
    refine Hs.loopN (c := .lt argCount ellR) hEc I args.length (40 * B + 44) ?_ ?_
    · intro k hk b ⟨h1, hout, hip, hram, hrc, hkin, hkout, hkc, hfr⟩
      have hbE : b.env ellR = args.length := (hfr ellR hE).trans hell
      have hcb : Cst b := Cst.of_fr hc hfr (by decide)
      refine ⟨by simp only [Cnd.eval, h1, hbE, decide_eq_true_eq]; exact hk, ?_⟩
      have hrcm : b.rc m = a.rc m + k := by rw [hrc]; simp
      have hrd : b.rc m < (b.ram m).length := by rw [hrcm, hram]; exact hlenm k hk
      show Hs C (.seq (.op (.rdM m t3)) (.seq emitNatO (.op (.inc argCount)))) b (40 * B + 44) (I (k + 1))
      refine Hs.mono (t := 1 + (40 * B + 40 + 1 + 1) + 1) ?_ (by omega) (fun x hx => hx)
      refine Hs.seq (hs_rdM C m t3 b hrd) (fun d hd => ?_)
      subst hd
      have hvk : (b.ram m).getD (b.rc m) 0 = args[k] := by rw [hrcm, hram]; exact hget k hk
      rw [hvk]
      have hcd : Cst ((b.set t3 args[k]).adv m) :=
        ⟨by show (b.set t3 args[k]).env vZ = 0; rw [DS.set_env_ne _ _ (by decide)]; exact hcb.z,
          by show (b.set t3 args[k]).env v1 = 1; rw [DS.set_env_ne _ _ (by decide)]; exact hcb.one,
          by show (b.set t3 args[k]).env v2 = 2; rw [DS.set_env_ne _ _ (by decide)]; exact hcb.two⟩
      have hd1t3 : ((b.set t3 args[k]).adv m).env t3 = args[k] := by
        show (b.set t3 args[k]).env t3 = args[k]; exact DS.set_env_self _ _ _
      have hBv : natBitLength args[k] ≤ B := hB _ (List.getElem_mem hk)
      have e := emitNatO_spec (C := C) ((b.set t3 args[k]).adv m) hcd hW (by rw [hd1t3]; omega)
      rw [hd1t3] at e
      refine Hs.seq (t1 := 40 * B + 40) (t2 := 1) (Hs.mono e (by omega) (fun x hx => hx)) (fun d2 hd2 => ?_)
      obtain ⟨o2, s2, c2, f2⟩ := hd2
      simp only [Prod.mk.injEq] at s2
      obtain ⟨ip2, ram2, rc2, kin2, kout2, kc2⟩ := s2
      have hcnt : d2.env argCount = k := by
        rw [f2 argCount (by decide)]
        show (b.set t3 args[k]).env argCount = k
        rw [DS.set_env_ne _ _ (by decide)]; exact h1
      refine Hs.mono (hs_inc C argCount d2 (by rw [hcnt]; omega)) le_rfl ?_
      rintro d3 rfl
      refine ⟨by rw [DS.set_env_self, hcnt], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [DS.set_out, o2]
        change b.out ++ natWord args[k] = _
        rw [hout, List.take_succ_eq_append_getElem hk, List.flatMap_append]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
      · rw [DS.set_ip, ip2]; exact hip
      · rw [DS.set_ram, ram2]; exact hram
      · rw [DS.set_rc, rc2]
        change Function.update b.rc m (b.rc m + 1) = _
        rw [hrcm, hrc, Function.update_idem]
        congr 1
      · rw [DS.set_kin, kin2]; exact hkin
      · rw [DS.set_kout, kout2]; exact hkout
      · rw [DS.set_kc, kc2]; exact hkc
      · intro y hy
        obtain ⟨hy3, hyN, hyA, -⟩ := scratch_facts hy
        rw [DS.set_env_ne _ _ hyA, f2 y hyN]
        show (b.set t3 args[k]).env y = a.env y
        rw [DS.set_env_ne _ _ hy3]; exact hfr y hy
    · intro b ⟨h1, _, _, _, _, _, _, _, hfr⟩
      have hbE : b.env ellR = args.length := (hfr ellR hE).trans hell
      simp only [Cnd.eval, h1, hbE, lt_self_iff_false, decide_false]
  refine Hs.mono (t := 1 + (args.length * ((40 * B + 44) + 2) + 2) + 1) ?_ (Nat.le_of_eq (by ring))
    (fun b hb => hb)
  refine Hs.seq (hs_zero C argCount a) (fun d hd => ?_)
  subst hd
  refine Hs.mono (hloop (a.set argCount 0) ⟨by simp, by simp, rfl, rfl, by simp, rfl, rfl, rfl,
    Fr.set a 0 (by simp [nodeScratch])⟩) le_rfl ?_
  rintro b ⟨-, hout, hip, hram, hrc, hkin, hkout, hkc, hfr⟩
  refine ⟨by rw [hout, List.take_length], hip, hram, hrc, hkin, hkout, hkc, Cst.of_fr hc hfr (by decide), hfr⟩

/-! ## One node, one runtime opcode emitter -/

/-- `argCount := 5` from the constant `2`. -/
def setFive : St VV MM := .seq (.op (.copy argCount v2)) (.seq (.op (.add argCount v2)) (.op (.inc argCount)))

theorem setFive_spec (a : DS VV MM) (hc : Cst a) (hW : 6 ≤ 2 ^ C.Wd) :
    Hs C setFive a 5 (· = a.set argCount 5) := by
  have h2 : a.env v2 = 2 := hc.two
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_copy C argCount v2 a (by decide)) (fun d0 h0 => ?_)
  subst h0
  have e0 : (a.set argCount (a.env v2)).env argCount = 2 := by rw [DS.set_env_self, h2]
  have e1 : (a.set argCount (a.env v2)).env v2 = 2 := by rw [DS.set_env_ne _ _ (by decide), h2]
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_add C argCount v2 _ (by decide) (by rw [e0, e1]; omega))
    (fun d1 h1 => ?_)
  subst h1
  rw [e0, e1]
  refine Hs.mono (hs_inc C argCount _ (by rw [DS.set_env_self]; omega)) le_rfl ?_
  rintro b rfl
  rw [DS.set_env_self, DS.set_set, DS.set_set]

/-- **The node emitter**: print the tag; if it is `5`, print the argument wires from store `m`, otherwise print
the two numeric fields. One program serves every node kind. -/
def emitNode (tagR leftR rightR ellR : Fin VV) (m : Fin MM) : St VV MM :=
  .seq (emitField tagR) (.seq setFive (.ite (.eq tagR argCount) (emitArgs ellR m) (emitPair leftR rightR)))

/-- The cost of one node with arity `ℓ` and fields of at most `B` bits. -/
def nodeCost (arity B : ℕ) : ℕ := (arity + 3) * (40 * B + 50)

/-- **One node word, exactly** (`Statement.lean:1484`). Registers `tagR leftR rightR` hold the three fields
(`nodeTag`, `nodeLeft`, `nodeRight`), `ellR` holds the arity, and for an oracle gate the store `m` holds its
argument wires from its cursor on. The output grows by exactly `oracleNodeWord nd`; the cursor of `m` advances by
the number of argument wires (`ℓ` for an oracle gate, `0` otherwise); nothing else outside `nodeScratch` changes. -/
theorem emitNode_spec {n arity : ℕ} (nd : OracleNode n arity) (tagR leftR rightR ellR : Fin VV)
    (hT : tagR ∉ nodeScratch) (hL : leftR ∉ nodeScratch) (hR : rightR ∉ nodeScratch) (hE : ellR ∉ nodeScratch)
    (m : Fin MM) (B : ℕ) (a : DS VV MM) (hc : Cst a) (hW : 3 ≤ C.Wd)
    (htag : a.env tagR = nodeTag nd) (hleft : a.env leftR = nodeLeft nd) (hright : a.env rightR = nodeRight nd)
    (hell : a.env ellR = arity) (harity : arity < 2 ^ C.Wd)
    (hmem : nodeArgs nd <+: (a.ram m).drop (a.rc m)) (hB : FieldsBound nd B) (hBW : B + 2 < 2 ^ C.Wd) :
    Hs C (emitNode tagR leftR rightR ellR m) a (nodeCost arity B) (fun b =>
      b.out = a.out ++ oracleNodeWord nd ∧ b.ip = a.ip ∧ b.ram = a.ram ∧
      b.rc = Function.update a.rc m (a.rc m + (nodeArgs nd).length) ∧ b.kin = a.kin ∧ b.kout = a.kout ∧
      b.kc = a.kc ∧ Cst b ∧ Fr a b nodeScratch) := by
  obtain ⟨hBt, hBl, hBr, hBa⟩ := hB
  obtain ⟨rest, hrest⟩ := hmem
  have h8 : 8 ≤ 2 ^ C.Wd := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) hW
  have hW2 : 2 ≤ C.Wd := by omega
  obtain ⟨hT3, -, hTA, hTf⟩ := scratch_facts hT
  obtain ⟨-, -, hLA, hLf⟩ := scratch_facts hL
  obtain ⟨-, -, hRA, hRf⟩ := scratch_facts hR
  obtain ⟨-, -, hEA, hEf⟩ := scratch_facts hE
  set T4 := arity * (40 * B + 46) + 80 * B + 89 with hT4
  have hcost : (40 * B + 42) + (5 + (T4 + 1) + 1) + 1 ≤ nodeCost arity B := by
    have h1 : arity * (40 * B + 46) ≤ arity * (40 * B + 50) := Nat.mul_le_mul_left _ (by omega)
    have h2 : nodeCost arity B = arity * (40 * B + 50) + 3 * (40 * B + 50) := by unfold nodeCost; ring
    omega
  refine Hs.mono (t := (40 * B + 42) + (5 + (T4 + 1) + 1) + 1) ?_ hcost (fun b hb => hb)
  refine Hs.seq (Hs.mono (emitField_spec tagR hT3 a hc hW2 (by rw [htag]; omega)) (t' := 40 * B + 42)
    (by rw [htag]; omega) (fun b hb => hb)) (fun d1 hd1 => ?_)
  obtain ⟨o1, i1, r1, c1, k1, k2, k3, cs1, f1⟩ := hd1
  rw [htag] at o1
  refine Hs.seq (setFive_spec d1 cs1 (by omega)) (fun d2 hd2 => ?_)
  subst hd2
  have cs2 : Cst (d1.set argCount 5) := Cst.of_fr cs1 (Fr.set d1 5 (T := [argCount]) (by simp)) (by decide)
  have hd2 : ∀ y, y ∉ nodeScratch → (d1.set argCount 5).env y = a.env y := by
    intro y hy
    obtain ⟨-, -, hyA, hyf⟩ := scratch_facts hy
    rw [DS.set_env_ne _ _ hyA, f1 y hyf]
  have fr2 : Fr a (d1.set argCount 5) nodeScratch := hd2
  have hd2tag : (d1.set argCount 5).env tagR = nodeTag nd := by rw [hd2 tagR hT, htag]
  by_cases h5 : nodeTag nd = 5
  · -- an oracle gate: the argument wires
    refine Hs.iteT (show tagR ≠ argCount from hTA)
      (by simp only [Cnd.eval, hd2tag, DS.set_env_self, h5, decide_true]) ?_
    have hlen := nodeArgs_length_of_eq nd h5
    have e := emitArgs_spec ellR hE m (nodeArgs nd) rest B (d1.set argCount 5) cs2 hW2
      (by rw [hd2 ellR hE, hell, hlen]) (by rw [hlen]; exact harity)
      (by rw [DS.set_ram, DS.set_rc, r1, c1]; exact hrest.symm) hBa hBW
    refine Hs.mono e (by rw [hlen]; omega) ?_
    rintro b ⟨o, i, r, c, kk1, kk2, kk3, cs, f⟩
    refine ⟨?_, by rw [i, DS.set_ip, i1], by rw [r, DS.set_ram, r1], by rw [c, DS.set_rc, c1],
      by rw [kk1, DS.set_kin, k1], by rw [kk2, DS.set_kout, k2], by rw [kk3, DS.set_kc, k3], cs, Fr.trans fr2 f⟩
    rw [o, DS.set_out, o1, oracleNodeWord_fields, if_pos h5, List.append_assoc]
  · -- a Boolean node: the two numeric fields
    refine Hs.iteF (show tagR ≠ argCount from hTA)
      (by simp only [Cnd.eval, hd2tag, DS.set_env_self, h5, decide_false]) ?_
    have e := emitPair_spec leftR rightR hLf hRf (d1.set argCount 5) cs2 hW2 B hBW
      (by rw [hd2 leftR hL, hleft]; exact hBl) (by rw [hd2 rightR hR, hright]; exact hBr)
    refine Hs.mono e (by omega) ?_
    rintro b ⟨o, i, r, c, kk1, kk2, kk3, cs, f⟩
    refine ⟨?_, by rw [i, DS.set_ip, i1], by rw [r, DS.set_ram, r1], ?_,
      by rw [kk1, DS.set_kin, k1], by rw [kk2, DS.set_kout, k2], by rw [kk3, DS.set_kc, k3], cs,
      Fr.trans fr2 (Fr.weaken f fieldScratch_sub)⟩
    · rw [o, DS.set_out, o1, hd2 leftR hL, hd2 rightR hR, hleft, hright, oracleNodeWord_fields, if_neg h5,
        List.append_assoc, List.append_assoc]
    · rw [c, DS.set_rc, c1, nodeArgs_of_ne nd h5, List.length_nil, Nat.add_zero, Function.update_eq_self]

/-- **One node of a circuit, streamed** (the closure the printing loop iterates): after the header and the first
`k` node words, printing node `k` yields the stream after `k + 1` nodes. -/
theorem emitNode_stream {ell : ℕ} (C0 : OracleCircuit ell ell) (k : ℕ) (hk : k < C0.nodes.length)
    (tagR leftR rightR ellR : Fin VV)
    (hT : tagR ∉ nodeScratch) (hL : leftR ∉ nodeScratch) (hR : rightR ∉ nodeScratch) (hE : ellR ∉ nodeScratch)
    (m : Fin MM) (a : DS VV MM) (hc : Cst a) (hW : 3 ≤ C.Wd)
    (hstream : a.out = streamWord C0 k)
    (htag : a.env tagR = nodeTag C0.nodes[k]) (hleft : a.env leftR = nodeLeft C0.nodes[k])
    (hright : a.env rightR = nodeRight C0.nodes[k]) (hell : a.env ellR = ell) (harity : ell < 2 ^ C.Wd)
    (hmem : nodeArgs C0.nodes[k] <+: (a.ram m).drop (a.rc m))
    (hBW : natBitLength (ell + C0.size + 5) + 2 < 2 ^ C.Wd) :
    Hs C (emitNode tagR leftR rightR ellR m) a (nodeCost ell (natBitLength (ell + C0.size + 5))) (fun b =>
      b.out = streamWord C0 (k + 1) ∧ b.ip = a.ip ∧ b.ram = a.ram ∧
      b.rc = Function.update a.rc m (a.rc m + (nodeArgs C0.nodes[k]).length) ∧ b.kin = a.kin ∧
      b.kout = a.kout ∧ b.kc = a.kc ∧ Cst b ∧ Fr a b nodeScratch) := by
  refine Hs.mono (emitNode_spec C0.nodes[k] tagR leftR rightR ellR hT hL hR hE m _ a hc hW htag hleft hright hell
    harity hmem (fieldsBound_of_circuit C0 k hk) hBW) le_rfl ?_
  rintro b ⟨o, rest⟩
  exact ⟨by rw [o, hstream, streamWord_succ C0 k hk], rest⟩

end NearCubicGates.Adapters.Compile.OraclePrint
