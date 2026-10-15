import Proof.Hierarchy.CompetitorSameBucketKeyAppend

/-! The signed-key appender on the same bounded local backing used by the
physical record decoders. The growing output is never padded or rewound. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketKeyAppend
open LocalBitMultitape SignedSortKey MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacities (cap : ℕ) : Fin 8 → ℕ := fun i => if i=6 then 0 else cap

def paddedCfg {s : ℕ} (q : Fin s) (payload : List Bool) (k right left cap : ℕ) (out : List Bool) : Configuration 8 s :=
  ZeroPadding.config (capacities cap) (cfg q payload k right left cap out)

theorem padded_run (payload : List Bool) (k right left cap : ℕ) (out : List Bool)
    (hp : 2*payload.length≤cap) (hk : 2*k≤cap) :
    ∃ r,runFrom machine (4*payload.length+8*k+13) (paddedCfg machine.start payload k right left cap out)=some r ∧
      r.final.heads=(paddedCfg machine.start payload k right left cap
        (out++frame (true::(payload++binary k right++binary k left)))).heads ∧
      r.final.tapes=(paddedCfg machine.start payload k right left cap
        (out++frame (true::(payload++binary k right++binary k left)))).tapes ∧
      r.steps≤4*payload.length+8*k+13 := by
  obtain ⟨base,hb,bh,bt,bs⟩ := append_run payload k right left cap out hp hk
  obtain ⟨actual,hr,hf,hs,_⟩ := ZeroPadding.run_config machine (capacities cap) _ _ base hb
  refine ⟨actual,hr,?_,?_,hs.trans_le bs⟩
  · rw [hf]
    exact bh
  · rw [hf]
    change (fun i => ZeroPadding.pad (capacities cap i) (base.final.tapes i))=_
    rw [bt]
    rfl

theorem padded_output (cap : ℕ) (payload : List Bool) (k right left : ℕ) (out : List Bool) :
    (paddedCfg machine.start payload k right left cap out).tapes 6=out := by
  simp [paddedCfg,ZeroPadding.config,capacities,cfg,ZeroPadding.pad]

theorem local_support (cap : ℕ) (payload : List Bool) (k right left : ℕ) (out : List Bool)
    (hp : 2*payload.length+1≤cap) (hk : 2*k+1≤cap) (i : Fin 8) (hi : i≠6) :
    ((paddedCfg machine.start payload k right left cap out).tapes i).length≤cap := by
  fin_cases i <;> simp_all [paddedCfg,ZeroPadding.config,capacities,cfg,ZeroPadding.pad_length]

def word (p k : ℕ) (coefficient : ℤ) (left right : ℕ) :=
  frame (RadixSemantics.word (CompetitorSameBucketKeys.key p k coefficient left right))

theorem signed_run (p k right left cap : ℕ) (coefficient : ℤ) (out : List Bool)
    (hp : 2*(p+1)≤cap) (hk : 2*k≤cap) :
    ∃ r,runFrom machine (4*p+8*k+17)
        (paddedCfg machine.start (signMagnitude p coefficient) k right left cap out)=some r ∧
      r.final.heads=(paddedCfg machine.start (signMagnitude p coefficient) k right left cap
        (out++word p k coefficient left right)).heads ∧
      r.final.tapes=(paddedCfg machine.start (signMagnitude p coefficient) k right left cap
        (out++word p k coefficient left right)).tapes ∧ r.steps≤4*p+8*k+17 := by
  have hword : frame (true::(signMagnitude p coefficient++binary k right++binary k left))=
      word p k coefficient left right := by rfl
  obtain ⟨r,hr,hh,ht,hs⟩ := padded_run (signMagnitude p coefficient) k right left cap out (by simpa using hp) hk
  have he : 4*(signMagnitude p coefficient).length+8*k+13=4*p+8*k+17 := by simp; omega
  rw [he] at hr hs
  rw [hword] at hh ht
  exact ⟨r,hr,hh,ht,hs⟩

end NearCubicWires.RepairOrdinary.CompetitorSameBucketKeyAppend
