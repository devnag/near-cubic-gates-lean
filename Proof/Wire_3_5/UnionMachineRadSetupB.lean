import Proof.Wire_3_5.PrimThrWRadSetup2

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.WireExponent3_5.PrimThrW.RadSetup NearCubicWires.WireExponent3_5.PrimThrW.RadSetup2
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists

/-! ## The request at explicit capacities -/

/-- **A Route-B RADIX request**: C2's request with an explicit scrub capacity `R`, log capacity `Lg` and loop
capacity `cap`. -/
structure RadReqB where
  r : RadReq
  R : ℕ
  Lg : ℕ
  cap : ℕ

/-- **The Route-B record** (computable): the setup fields at `R`, `Lg`, `cap`, then the factor blocks in store order. -/
def RadReqB.record (q : RadReqB) : List Bool :=
  fieldsWord (setupFieldsG (19 + 1) q.R q.Lg (radEv q.r.D.M (2 * q.r.digs.length) (radCs q.r.D q.r.digs q.r.p q.r.b0)
    (radT q.r.digs q.r.p q.r.s) q.cap)) ++ ((radBlocksC q.r.D q.r.digs).flatMap (fun b => true :: b) ++ [false])

/-- **The row's capacity conditions** (`radRow_step`'s, computable). -/
structure RadReqB.Caps (q : RadReqB) : Prop where
  R2 : 2 ≤ q.R
  Rx : ∀ dg ∈ q.r.digs, ∀ t ≤ q.r.D.M, ∀ sgn : Bool, costC q.r.D dg.1 t sgn false dg.2 + 1 ≤ q.R
  RL : q.R + 1 ≤ q.Lg
  c0 : 2 * q.r.digs.length * (q.r.D.M + 1) * (4 * q.R + 9) + 1 ≤ q.cap
  c1 : resLoopCost (radCs q.r.D q.r.digs q.r.p q.r.b0) + 3 ≤ q.cap
  c2 : mselCost (radFs q.r.D q.r.digs) ≤ q.cap
  c3 : incCost q.r.D.M (2 * q.r.digs.length) ≤ q.cap

/-- The row's cost bound at the Route-B record (`radRowCost_bound`'s). -/
def RadReqB.bound (q : RadReqB) : ℕ :=
  (q.r.D.M + 1) ^ (2 * q.r.digs.length) * (128 * (q.record.length + 1) ^ 2)

/-- **The Route-B record is the record `radRow_step` runs on.** -/
theorem record_eq (q : RadReqB) (hok : DigsOk q.r.digs) :
    radRowRec q.r.D.M (2 * q.r.digs.length) (radCs q.r.D q.r.digs q.r.p q.r.b0) (radT q.r.digs q.r.p q.r.s) q.R q.Lg
      q.cap (radSpecs q.r.D q.r.digs hok) = q.record := by
  unfold radRowRec RadReqB.record
  rw [storeRec_radSpecs]
  rfl

/-- **The capacity conditions give `radRow_step`'s hypotheses** at `radSpecs`. -/
theorem caps_step (q : RadReqB) (hok : DigsOk q.r.digs) (hc : q.Caps) :
    (∀ x ∈ radSpecs q.r.D q.r.digs hok, x.cost + 1 ≤ q.R) ∧ storeCost (radSpecs q.r.D q.r.digs hok) q.R ≤ q.cap ∧
      mselCost ((radSpecs q.r.D q.r.digs hok).map FSpec.poly) ≤ q.cap := by
  have hRx : ∀ x ∈ radSpecs q.r.D q.r.digs hok, x.cost + 1 ≤ q.R := by
    intro x hx
    obtain ⟨dg, hdg, t, ht, sgn, hl, rfl⟩ := mem_radSpecs q.r.D q.r.digs hok x hx
    have h1 := visitSpec_cost_le q.r.D dg.1 (min t q.r.D.M) sgn (min_le_right _ _) false dg.2 hl
    have e : costC q.r.D dg.1 (min t q.r.D.M) sgn false dg.2 = costC q.r.D dg.1 t sgn false dg.2 := by
      rw [min_eq_left ht]
    have h2 := hc.Rx dg hdg t ht sgn
    omega
  refine ⟨hRx, ?_, ?_⟩
  · have h := storeCost_le (radSpecs q.r.D q.r.digs hok) q.R hRx
    rw [radSpecs_length] at h
    have := hc.c0
    omega
  · have hmp : (radSpecs q.r.D q.r.digs hok).map FSpec.poly = radFs q.r.D q.r.digs := by
      rw [radSpecs_poly q.r.D q.r.digs hok []]; rfl
    rw [hmp]
    exact hc.c2

/-! ## The ready state -/

/-- **A Route-B RADIX-ready cell state**: `Joins.RadReady` with the Route-B record `frame q.record` on stream `3`, the
request admissible (`RadReq.Pre`) and the row's capacity conditions. -/
structure RadReadyB (x : ℕ) (σ : WState (LNS x) LNR) (w out : List Bool) (j : ℕ) (u : List Bool) (q : RadReqB) :
    Prop where
  s0 : σ.st (sk x 0) = frame w
  h0 : σ.sh (sk x 0) = 0
  s1 : σ.st (sk x 1) = out ++ [false]
  h1 : σ.sh (sk x 1) = out.length
  s2 : σ.st (sk x 2) = List.replicate j true
  h2 : σ.sh (sk x 2) = 0
  s3 : σ.st (sk x 3) = frame q.record
  h3 : σ.sh (sk x 3) = 0
  s113 : σ.st (sk x 113) = u
  h113 : σ.sh (sk x 113) = 0
  s150 : σ.st (sk x 150) = [true]
  h150 : σ.sh (sk x 150) = 0
  blank : ∀ k : Fin 161, k.val ≠ 0 → k.val ≠ 1 → k.val ≠ 2 → k.val ≠ 3 → k.val ≠ 113 → k.val ≠ 150 →
    σ.st (sk x k) = [] ∧ σ.sh (sk x k) = 0
  blankT : ∀ k : Fin x, σ.st (sT x k) = [] ∧ σ.sh (sT x k) = 0
  pre : q.r.Pre
  caps : q.Caps

/-! ## The setup -/

/-- **The RADIX row setup, Route B**: `RadSetup2.RadSetupSpec2` ending in `RadReadyB` at some
capacities for `radReqOf … g pr s row`, with the pipe's bound `q.bound ≤ pipe n` (`pipe` quasi-bounded). -/
structure RadSetupSpecB (x : ℕ) (l : Literals) (F : GateFree l) where
  s : ℕ
  M : Machine (LNS x + 2 + LNR) s
  need : ℕ → ℕ
  bound : ℕ → ℕ
  pipe : ℕ → ℕ
  Cn : ℕ
  Dn : ℕ
  Kn : ℕ
  need_q : ∀ n, QuasiBounded (need n) n Cn Dn Kn
  Cb : ℕ
  Db : ℕ
  Kb : ℕ
  bound_q : ∀ n, QuasiBounded (bound n) n Cb Db Kb
  Cp : ℕ
  Dp : ℕ
  Kp : ℕ
  pipe_q : ∀ n, QuasiBounded (pipe n) n Cp Dp Kp
  run : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    (a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ (g : ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg)
      (pr : SupplierPrime.PrimeIndex (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))
      (s : ZMod pr.val) (row : ℕ),
    row < (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) ^ 2 →
    ∀ (cap : ℕ) (out : List Bool) (j : ℕ) (u : List Bool) (σ : WState (LNS x) LNR),
    RsIn2 x σ ((thrReq n a' ha' Cs carriers translation).word ++
        frame (List.ofFn (FinalPass.thrHashBits ((callInputs l F kclk coef A a ha).starParams n hs)
          (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) Cs carriers
          ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg
          (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
          (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
          (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
          (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers))))
      out j u
      (radVals l F kclk coef A a ha hs Cs carriers
        ((Enum.thrEqEquiv ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg g).val) pr.val s.val
        row)
      (Data.unaryList (primesList (callNums l F kclk coef A a ha hs Cs carriers).cut))
      (winRecs (thrMP (callNums l F kclk coef A a ha hs Cs carriers).M (callNums l F kclk coef A a ha hs Cs carriers).A
        (callNums l F kclk coef A a ha hs Cs carriers).Bs (callNums l F kclk coef A a ha hs Cs carriers).den))
      (frame (SignedSortKey.binary (callNums l F kclk coef A a ha hs Cs carriers).ell0
        (callNums l F kclk coef A a ha hs Cs carriers).pMod))
      carriers.length ((callInputs l F kclk coef A a ha).filterParams .thr n).cap →
    need n ≤ cap →
    ∃ (σR : WState (LNS x) LNR) (m : ℕ) (q : RadReqB),
      Step M m (wenc cap σ).H (wenc cap σ).A (wenc cap σR).H (wenc cap σR).A ∧ m ≤ bound n ∧
      q.r = radReqOf l F kclk coef A a ha hs Cs carriers translation g pr s row ∧ q.bound ≤ pipe n ∧
      RadReadyB x σR ((thrReq n a' ha' Cs carriers translation).word ++
        frame (List.ofFn (FinalPass.thrHashBits ((callInputs l F kclk coef A a ha).starParams n hs)
          (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) Cs carriers
          ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg
          (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
          (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
          (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
          (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers))))
        out j u q

end NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB
