/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.Security.RbrGame
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.ProofSystem.Logup.Security.Common
import ArkLib.ToVCVio.OracleComp.Coercions.SubSpec

/-!
# LogUp Completeness

Completeness statements for Protocol 2 of Haböck's LogUp lookup argument (Cryptology ePrint
Archive, Paper 2022/1530, <https://eprint.iacr.org/2022/1530>).
-/

open scoped NNReal

namespace Logup

section Completeness

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

local instance instOuterChallengeOracleInterface' :
    (i : (outerPSpec F n params).ChallengeIdx) →
      OracleInterface ((outerPSpec F n params).Challenge i) :=
  ProtocolSpec.challengeOracleInterface

/-! ## Helper Lemmas

This section collects the shared estimates and support-manipulation facts used by the phase
completeness proofs.  The algebraic identities used by honest LogUp data live in
`Logup/Algebra.lean`; the lemmas here are about probabilities, support membership, and peeling
simulated oracle computations. -/

/-- Completeness error from the current `x`-sampling model: the verifier samples `x` from all of
`F`. Following Remark 3 of the LogUp paper, table-pole challenges are treated as bad inputs for
the honest handoff rather than rejected by an exponential verifier scan. -/
noncomputable def logupCompletenessError (F : Type) [Fintype F] (n : ℕ) : ℝ≥0 :=
  (Fintype.card (Fin n → Fin 2) : ℝ≥0) / (Fintype.card F)

omit [DecidableEq F] in
/-- A uniformly sampled outer challenge avoids all table denominator poles with probability at
least `1 - logupCompletenessError`.

The bad challenges are exactly negatives of table values on Boolean rows, so their count is bounded
by the hypercube size. -/
private theorem uniform_avoids_table_poles_prob [Inhabited F]
    (oStmt : ∀ i, OStmtIn F n M i) :
    (1 : ENNReal) - (logupCompletenessError F n : ENNReal) ≤
      Pr[fun x : F => ∀ u : (Fin n → Fin 2),
        x + MvPolynomial.toEvalsZeroOne (oStmt .table).1 u ≠ 0 | $ᵗ F] := by
  classical
  let _ : DecidableEq F := Classical.decEq F
  let bad : F → Prop :=
    fun x => ∃ u : (Fin n → Fin 2), x + MvPolynomial.toEvalsZeroOne (oStmt .table).1 u = 0
  have hbad :
      Pr[bad | $ᵗ F] ≤ (logupCompletenessError F n : ENNReal) := by
    rw [probEvent_uniformSample]
    unfold logupCompletenessError
    have hcard :
        ((Finset.univ.filter bad).card : ENNReal) ≤
          (Fintype.card (Fin n → Fin 2) : ENNReal) := by
      exact_mod_cast (by
        simpa [bad] using
          pole_card_le (F := F) (n := n) (table := MvPolynomial.toEvalsZeroOne (oStmt .table).1))
    convert ENNReal.div_le_div_right hcard (Fintype.card F : ENNReal) using 1; norm_num
  have hcompl :
      Pr[fun x : F => ¬ bad x | $ᵗ F] + Pr[bad | $ᵗ F] = (1 : ENNReal) := by
    have h := probEvent_compl ($ᵗ F) (fun x : F => ¬ bad x)
    simpa [bad, probFailure_uniformSample, not_not] using h
  rw [tsub_le_iff_right]
  calc
    (1 : ENNReal) = Pr[fun x : F => ¬ bad x | $ᵗ F] + Pr[bad | $ᵗ F] := hcompl.symm
    _ ≤ Pr[fun x : F => ¬ bad x | $ᵗ F] + (logupCompletenessError F n : ENNReal) :=
        add_le_add le_rfl hbad
  · apply le_of_eq
    congr
    funext x
    simp [bad]

/-- Lower-bound a bind event by proving the same lower bound for every supported first-stage
output.

This is the completeness-side bind rule used after peeling a deterministic prefix of a computation:
if the prefix does not fail and every reachable continuation succeeds with probability at least
`r`, then the whole bind succeeds with probability at least `r`. -/
private theorem le_probEvent_bind_of_forall_le {m : Type → Type*} [Monad m] [LawfulMonad m]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [MonadLiftT m SetM]
    [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    {α β : Type} {mx : m α} {my : α → m β} {q : β → Prop} {r : ENNReal}
    (hfail : Pr[⊥ | mx] = 0) (h : ∀ x ∈ support mx, r ≤ Pr[ q | my x]) :
    r ≤ Pr[ q | mx >>= my] := by
  have htrue : Pr[fun _ : α => True | mx] = (1 : ENNReal) := by
    exact probEvent_eq_one (mx := mx) (p := fun _ : α => True) ⟨hfail, by simp⟩
  have hmul := mul_le_probEvent_bind (mx := mx) (my := my)
    (p := fun _ : α => True) (q := q) (r := 1) (r' := r)
    (by simp [htrue]) (fun x hx _ => h x hx)
  simpa using hmul

/-- A successful full reduction run contains a prover transcript that was produced by the prover.

Completeness of the lifted sumcheck phase needs this to apply the generic sumcheck prover-side
oracle-statement preservation theorem to the transcript extracted from the reduction run. -/
private theorem reduction_run_prover_mem {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn)
    (tr : pSpec.FullTranscript) (out : StmtOut) (witOut : WitOut) (verOut : StmtOut)
    (h : some ((tr, out, witOut), verOut) ∈ support (R.run stmt wit).run) :
    (tr, out, witOut) ∈ support (Prover.run stmt wit R.prover) := by
  simp only [ProtocolSpec.ChallengeIdx, ProtocolSpec.Challenge, Reduction.run, bind_pure_comp,
    OptionT.run_bind, OptionT.run_monadLift, monadLift_self,
    OptionT.run_map, Option.elimM_map, Option.elim_some,
    support_bind, Set.mem_iUnion, exists_prop, Prod.exists] at h
  rcases h with ⟨a, a_1, b, hp, hv⟩
  suffices hEq : (a, a_1, b) = (tr, out, witOut) by
    simpa [hEq] using hp
  simp only [Option.elimM, support_bind, Set.mem_iUnion, exists_prop] at hv
  rcases hv with ⟨i, _hi, hv⟩
  cases i with
  | none => simp at hv
  | some verCandidate =>
      simp only [Option.elim_some, support_map, Set.mem_image, Option.map_eq_some_iff,
        Prod.mk.injEq, exists_eq_right_right, ↓existsAndEq, true_and] at hv
      rcases hv with ⟨_, rfl, rfl, rfl⟩
      rfl

local macro "peel_sim_map " h:ident " with " pat:rcasesPat : tactic =>
  `(tactic|
    (erw [simulateQ_map, StateT.run_map] at $h:ident
     rw [support_map, Set.mem_image] at $h:ident
     obtain $pat := $h))

local macro "peel_sim_bind " h:ident " with " pat:rcasesPat : tactic =>
  `(tactic|
    (erw [simulateQ_bind, StateT.run_bind] at $h:ident
     rw [mem_support_bind_iff] at $h:ident
     obtain $pat := $h))

omit oSpec σ init impl [SampleableType F] in
/-- Honest multiplicities and helpers satisfy the outer-to-sumcheck handoff whenever the sampled
challenge avoids every table pole. Kept separate from the execution proof so Lean does not have to
normalize the four-round probabilistic computation while checking the algebraic argument. -/
private theorem honestOuterOutput_mem_logupMidRelation
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (x : F) (batch : BatchingChallenge F n params.numGroups)
    (hIn : ((stmt, oStmt), PUnit.unit) ∈ inputRelation F n M)
    (hNoTablePoles : ∀ u : Fin n → Fin 2,
      x + MvPolynomial.toEvalsZeroOne (oStmt .table).1 u ≠ 0) :
    (({ xChallenge := x, zChallenge := batch.1, batchingScalars := batch.2 },
        fun
          | .input i => oStmt i
          | .multiplicity => honestMultiplicity oStmt
          | .helpers => honestHelpers params oStmt x), ()) ∈
      logupMidRelation F n M params := by
  have hcols : ∀ j : Fin M, ∀ u : Fin n → Fin 2, ∃ v : Fin n → Fin 2,
      MvPolynomial.toEvalsZeroOne (oStmt (.column j)).1 u =
        MvPolynomial.toEvalsZeroOne (oStmt .table).1 v := by
    simpa [inputRelation] using hIn
  have hchar : ∀ a : F,
      lookupMultiplicityCount
          (fun j => MvPolynomial.toEvalsZeroOne (oStmt (.column j)).1) a ≠ 0 →
        (tableMultiplicityCount (MvPolynomial.toEvalsZeroOne (oStmt .table).1) a : F) ≠ 0 :=
    fun _ hlookup =>
      tableMultiplicityCount_cast_ne_zero_of_lookupMultiplicityCount_ne_zero
        stmt.charLarge (MvPolynomial.toEvalsZeroOne (oStmt .table).1)
        (fun j => MvPolynomial.toEvalsZeroOne (oStmt (.column j)).1) hcols hlookup
  have hpoles : ∀ (i : TermIdx M) (u : Fin n → Fin 2),
      termPhi (MvPolynomial.toEvalsZeroOne (oStmt .table).1)
        (fun j => MvPolynomial.toEvalsZeroOne (oStmt (.column j)).1) x i u ≠ 0 :=
    termPhi_ne_zero_of_table_poles (MvPolynomial.toEvalsZeroOne (oStmt .table).1)
      (fun j => MvPolynomial.toEvalsZeroOne (oStmt (.column j)).1) x hcols hNoTablePoles
  let stmtAfter : StmtAfterOuter F n M params :=
    { xChallenge := x, zChallenge := batch.1, batchingScalars := batch.2 }
  let oStmtAfter : ∀ i, OStmtAfterOuter F n M params i :=
    fun
      | .input i => oStmt i
      | .multiplicity => honestMultiplicity oStmt
      | .helpers => honestHelpers params oStmt x
  have hMultiplicity :
      MvPolynomial.toEvalsZeroOne (honestMultiplicity oStmt).1 =
        normalizedMultiplicityValue (MvPolynomial.toEvalsZeroOne (oStmt .table).1)
          (fun i => MvPolynomial.toEvalsZeroOne (oStmt (.column i)).1) := by
    change (MvPolynomial.MLEEquiv (R := F) (σ := Fin n)) (honestMultiplicity oStmt) = _
    simp [honestMultiplicity]
  have hHelpers :
      (fun k => MvPolynomial.toEvalsZeroOne (honestHelpers params oStmt x k).1) =
        fun k u =>
          helperValue params.group (MvPolynomial.toEvalsZeroOne (oStmt .table).1)
            (fun i => MvPolynomial.toEvalsZeroOne (oStmt (.column i)).1)
            (normalizedMultiplicityValue (MvPolynomial.toEvalsZeroOne (oStmt .table).1)
              (fun i => MvPolynomial.toEvalsZeroOne (oStmt (.column i)).1))
            x k u := by
    funext k
    change (MvPolynomial.MLEEquiv (R := F) (σ := Fin n))
        (honestHelpers params oStmt x k) = _
    simp [honestHelpers, hMultiplicity]
  have hmid : ((stmtAfter, oStmtAfter), ()) ∈ logupMidRelation F n M params := by
    unfold logupMidRelation logupOuterSumcheckClaim
    rw [← logupOuterClaim_zero
      (groups := params.group)
      (hgroups := sum_protocolGroups (F := F) (M := M) params)
      (table := MvPolynomial.toEvalsZeroOne (oStmt .table).1)
      (columns := fun j => MvPolynomial.toEvalsZeroOne (oStmt (.column j)).1)
      (xChallenge := x) (zChallenge := batch.1) (batchingScalars := batch.2)
      hchar hpoles]
    apply Finset.sum_congr rfl
    intro u _
    rw [logupQPolynomial_eval_hypercube]
    simp [stmtAfter, oStmtAfter, hMultiplicity, hHelpers]
  simpa [stmtAfter, oStmtAfter] using hmid

/-- Output type of the concrete outer-phase completeness experiment. -/
private abbrev OuterCompletenessOutput :=
  (((outerPSpec F n params).FullTranscript ×
      (StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)) × Unit) ×
    (StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)))

/-- Concrete experiment used by outer-phase completeness. -/
private noncomputable def outerCompletenessGame
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i) :
    OptionT ProbComp (OuterCompletenessOutput F n M params) :=
  OptionT.mk do
    let s ← init
    (simulateQ
      (QueryImpl.addLift impl ProtocolSpec.challengeQueryImpl :
        QueryImpl (oSpec + [(outerPSpec F n params).Challenge]ₒ) (StateT σ ProbComp))
      ((outerOracleReduction oSpec F n M params).toReduction.run (stmt, oStmt) ()).run).run' s

/-- The outer challenge avoids all table poles in a successful completeness experiment. -/
private def outerChallengeIsGood (oStmt : ∀ i, OStmtIn F n M i)
    (out : OuterCompletenessOutput F n M params) : Prop :=
  ∀ u : Fin n → Fin 2,
    out.2.1.xChallenge + MvPolynomial.toEvalsZeroOne (oStmt .table).1 u ≠ 0

set_option maxHeartbeats 1000000 in
-- Expanding the concrete four-round probability experiment requires substantial normalization.
/-- The honest outer experiment samples a good table-pole challenge with the advertised
probability. This is separated from output correctness to keep each elaboration task bounded. -/
private theorem outerChallengeIsGood_probability [Inhabited F]
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i) :
    Pr[outerChallengeIsGood F n M params oStmt |
        outerCompletenessGame oSpec F n M params init impl stmt oStmt] ≥
      1 - logupCompletenessError F n := by
  unfold outerChallengeIsGood outerCompletenessGame
  simp only [outerOracleReduction, OracleReduction.toReduction, Reduction.run, Prover.run,
    Verifier.run, Prover.runToRound, outerProver, Fin.induction_four,
    Prover.processRound, outerPSpec]
  repeat' split <;> rename_i hd <;> first | exact absurd hd (by decide) | skip
  have hchallenge (i : (outerPSpec F n params).ChallengeIdx) :
      simulateQ
          (impl.addLift ProtocolSpec.challengeQueryImpl :
            QueryImpl (oSpec + [(outerPSpec F n params).Challenge]ₒ) (StateT σ ProbComp))
          (liftM ((outerPSpec F n params).getChallenge i)) =
        (liftM ($ᵗ ((outerPSpec F n params).Challenge i)) :
          StateT σ ProbComp ((outerPSpec F n params).Challenge i)) := by
    rw [← OracleComp.liftComp_eq_liftM]
    exact ProtocolSpec.simulateQ_addLift_challengeQueryImpl_getChallenge impl i
  have hchallengeRaw (i : (outerPSpec F n params).ChallengeIdx) :
      simulateQ
          (impl + QueryImpl.liftTarget (StateT σ ProbComp)
            (ProtocolSpec.challengeQueryImpl (pSpec := outerPSpec F n params)))
          (liftM
            ((liftM (OracleSpec.query
              (spec := [(outerPSpec F n params).Challenge]ₒ) ⟨i, ()⟩)) :
                OracleComp [(outerPSpec F n params).Challenge]ₒ
                  ((outerPSpec F n params).Challenge i))) =
        (liftM ($ᵗ ((outerPSpec F n params).Challenge i)) :
          StateT σ ProbComp ((outerPSpec F n params).Challenge i)) := by
    exact hchallenge i
  refine le_trans (uniform_avoids_table_poles_prob (F := F) (n := n) (M := M) oStmt) ?_
  rw [OptionT.mk_bind]
  apply le_probEvent_bind_of_forall_le
  · simp
  · intro s hs
    clear hs
    simp only [OptionT.run_bind, Option.elimM,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, bind_pure_comp, simulateQ_bind,
      StateT.run'_eq, StateT.run_bind, Function.comp_apply]
    erw [simulateQ_bind]
    erw [simulateQ_bind]
    rw [StateT.run_bind]
    erw [simulateQ_pure]
    simp only [pure_bind]
    erw [simulateQ_bind]
    rw [hchallenge]
    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind,
      bind_assoc, OptionT.mk_bind]
    · change _ ≤ Pr[_ | (liftM ($ᵗ F : ProbComp F) : OptionT ProbComp F) >>= _]
      simpa [probEvent_uniformSample] using
        (mul_le_probEvent_bind
          (mx := (liftM ($ᵗ F : ProbComp F) : OptionT ProbComp F))
          (p := fun x : F => ∀ u : Fin n → Fin 2,
            x + MvPolynomial.toEvalsZeroOne (oStmt .table).1 u ≠ 0)
          (r := Pr[fun x : F => ∀ u : Fin n → Fin 2,
            x + MvPolynomial.toEvalsZeroOne (oStmt .table).1 u ≠ 0 | $ᵗ F])
          (r' := 1) (by simp) (by
            intro x hx hGood
            erw [simulateQ_pure]
            simp only [outerProverState, StateT.run_pure, liftM_pure, pure_bind]
            erw [hchallengeRaw]
            simp only [StateT.run_monadLift, monadLift_self, bind_pure_comp,
              simulateQ_pure, StateT.run_pure, liftM_pure, pure_bind,
              OracleVerifier.toVerifier, OptionT.run_mk,
              OptionT.run_pure, map_pure, Option.map_some, Option.elim_some,
              Option.getM_some, outerVerifier, outerChallengeXIdx,
              outerChallengeBatchIdx, OracleVerifier.materializeOutput,
              OracleVerifier.materializeOutputOracle, ProtocolSpec.FullTranscript.challenges,
              ProtocolSpec.FullTranscript.messages, ProtocolSpec.Transcript.concat, Fin.snoc,
              ProtocolSpec.take_Type, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
              Nat.reduceAdd, Fin.vcons_fin_zero, Nat.one_mod, Nat.mod_succ, Nat.one_lt_ofNat,
              ↓reduceDIte, Fin.reduceSucc, Fin.reduceCastLT, Fin.castSucc_one,
              Order.lt_two_iff, Std.le_refl, lt_self_iff_false, Fin.succ_one_eq_two,
              Fin.reduceLast, ProtocolSpec.MessageIdx, ProtocolSpec.Message,
              Fin.castSucc_castLT, Fin.val_castLT, Order.lt_one_iff, Fin.val_eq_zero_iff,
              Nat.zero_mod, Fin.val_eq_zero, Fin.succ_zero_eq_one]
            rw [one_le_probEvent_iff, probEvent_eq_one_iff]
            constructor
            · rw [probFailure_bind_eq_zero_iff]
              constructor
              · simp [OptionT.probFailure_liftM]
              · intro batchState hbatch
                clear hbatch
                simp [OptionT.probFailure_eq]
            · intro out hout
              rw [mem_support_bind_iff] at hout
              obtain ⟨batchState, _hbatch, hout⟩ := hout
              rw [OptionT.mem_support_iff] at hout
              simp only [OptionT.run_mk, support_pure, Set.mem_singleton_iff,
                Option.some.injEq] at hout
              subst out
              intro u
              convert hGood u using 1
              rfl))

-- The proof peels the whole four-round outer transcript and reconstructs the handoff relation;
-- the generated support terms are large even though the reasoning is deterministic.

/-! ## Outer Phase Completeness

The honest outer prover sends multiplicities and helpers, samples the outer challenges, and reaches
the LogUp-to-sumcheck handoff relation except when the sampled `x` challenge hits a table pole. -/

set_option maxHeartbeats 1000000 in
-- Peeling the concrete four-round transcript requires substantial dependent normalization.
/-- Completeness of the outer LogUp phase: the honest outer prover reaches the zero-sum handoff
relation, except with the pole-sampling error. -/
theorem logup_outer_completeness [Inhabited F] :
    (outerOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) (logupMidRelation F n M params) (logupCompletenessError F n) := by
  unfold OracleReduction.completeness Reduction.completeness
  rintro ⟨stmt, oStmt⟩ ⟨⟩ hIn
  have hGoodProbability :=
    outerChallengeIsGood_probability oSpec F n M params init impl stmt oStmt
  simp only [outerOracleReduction, OracleReduction.toReduction, Reduction.run, Prover.run,
    Verifier.run, Prover.runToRound, outerProver, Fin.induction_four,
    Prover.processRound, outerPSpec]
  repeat' split <;> rename_i hd <;> first | exact absurd hd (by decide) | skip
  simp only [ProtocolSpec.getChallenge, liftM, monadLift, MonadLift.monadLift,
    MonadLiftT.monadLift, OracleComp.liftComp_pure, bind_pure_comp, map_pure,
    QueryImpl.addLift_def]
  refine ge_trans (probEvent_mono
    (p := fun out => ∀ u : (Fin n → Fin 2),
      out.2.1.xChallenge + MvPolynomial.toEvalsZeroOne (oStmt .table).1 u ≠ 0)
    ?goodOutputs) ?goodProb
  · -- every output with a non-pole outer challenge satisfies the success predicate
    intro out hout hGood
    rw [OptionT.mem_support_iff] at hout
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hout
    obtain ⟨s, -, hout⟩ := hout
    simp only [StateT.run'_eq, support_map, Set.mem_image] at hout
    obtain ⟨⟨_, s'⟩, hout, rfl⟩ := hout
    peel_sim_bind hout with ⟨⟨pres, s2⟩, hpres, hver⟩
    simp only [OptionT.lift, OptionT.mk] at hpres
    peel_sim_bind hpres with ⟨⟨pval, sp⟩, hpval, hpeq⟩
    peel_sim_map hpval with ⟨⟨a, sa⟩, ha, hpval_eq⟩
    peel_sim_bind ha with ⟨⟨b, sb⟩, hb, ha3⟩
    peel_sim_bind ha3 with ⟨⟨zlam, szlam⟩, hzlam, ha3eq⟩
    erw [simulateQ_map, simulateQ_pure, StateT.run_pure] at ha3eq
    rw [support_pure, Set.mem_singleton_iff] at ha3eq
    -- round 1: peel `hb` to reach the `x` challenge query
    peel_sim_map hb with ⟨⟨c, sc⟩, hc, hbeq⟩
    peel_sim_bind hc with ⟨⟨d, sd⟩, hd, hc2⟩
    peel_sim_bind hc2 with ⟨⟨xval, sx⟩, hx, hc2eq⟩
    erw [simulateQ_map, simulateQ_pure, StateT.run_pure] at hc2eq
    rw [support_pure, Set.mem_singleton_iff] at hc2eq
    -- round 0 is deterministic (a pure `honestMultiplicity` send)
    erw [simulateQ_pure, StateT.run_pure] at hd
    rw [support_pure, Set.mem_singleton_iff] at hd
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hd
    -- substitute the prover-side equation chain to make `pval`/`pres` concrete
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc2eq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hbeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha3eq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpval_eq
    erw [simulateQ_pure, StateT.run_pure] at hpeq
    rw [support_pure, Set.mem_singleton_iff] at hpeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpeq
    change F at xval
    change BatchingChallenge F n params.numGroups at zlam
    -- peel the verifier (match on `some pval` resolves; then its bind)
    simp only at hver
    erw [simulateQ_bind, StateT.run_bind] at hver
    rw [mem_support_bind_iff] at hver
    obtain ⟨⟨vstmt, sv⟩, hverify, hvout⟩ := hver
    -- The scan-free verifier packages the sampled challenges; the non-pole assumption comes from
    -- the good-challenge event above.
    let tr : (outerPSpec F n params).FullTranscript :=
      ProtocolSpec.Transcript.concat (pSpec := outerPSpec F n params) (m := 3) zlam
        (ProtocolSpec.Transcript.concat (pSpec := outerPSpec F n params) (m := 2)
          (honestHelpers params oStmt xval)
          (ProtocolSpec.Transcript.concat (pSpec := outerPSpec F n params) (m := 1) xval
            (ProtocolSpec.Transcript.concat (pSpec := outerPSpec F n params) (m := 0)
              (honestMultiplicity oStmt)
              (default : ProtocolSpec.Transcript (0 : Fin 5) (outerPSpec F n params)))))
    have hrun :
        ((outerVerifier oSpec F n M params).toVerifier).verify (stmt, oStmt) tr =
          (pure
            ({ xChallenge := xval, zChallenge := zlam.1, batchingScalars := zlam.2 },
              fun
                | .input i => oStmt i
                | .multiplicity => honestMultiplicity oStmt
                | .helpers => honestHelpers params oStmt xval) :
            OptionT (OracleComp oSpec)
              (StmtAfterOuter F n M params ×
                (∀ i, OStmtAfterOuter F n M params i))) := by
      unfold OracleVerifier.toVerifier
      simp only
      have hVerifyRun := congrArg OptionT.run
        (outerVerify_simulateQ_eq (oSpec := oSpec) (F := F) (n := n) (M := M)
          (params := params) stmt oStmt
          (ProtocolSpec.FullTranscript.messages tr)
          (ProtocolSpec.FullTranscript.challenges tr))
      change simulateQ (OracleInterface.simOracle2 oSpec oStmt tr.messages)
        ((outerVerifier oSpec F n M params).verify stmt tr.challenges).run = _ at hVerifyRun
      simp only [OptionT.run_pure] at hVerifyRun
      rw [hVerifyRun]
      simp only [OStmtAfterOuter, OStmtIn, MultiplicityMessage, HelperMessages,
        map_pure, Option.map_some]
      congr
      funext i
      cases i <;> rfl
    dsimp [tr] at hrun
    rw [hrun] at hverify
    simp only [OptionT.run_pure, OptionT.run_lift] at hverify
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hverify
    -- The honest verifier output is now concrete, so the final bind is deterministic.
    simp only [Option.getM_some, map_pure] at hvout
    obtain ⟨rfl, rfl⟩ := hvout
    have hNoTablePoles :
        ∀ u : (Fin n → Fin 2),
          xval + MvPolynomial.toEvalsZeroOne (oStmt .table).1 u ≠ 0 := by
      intro u
      simpa [outerVerifier, outerChallengeXIdx, outerChallengeBatchIdx,
        ProtocolSpec.FullTranscript.challenges, ProtocolSpec.Transcript.concat, Fin.snoc]
        using hGood u
    let stmtAfter : StmtAfterOuter F n M params :=
      { xChallenge := xval, zChallenge := zlam.1, batchingScalars := zlam.2 }
    let oStmtAfter : ∀ i, OStmtAfterOuter F n M params i :=
      fun
        | .input i => oStmt i
        | .multiplicity => honestMultiplicity oStmt
        | .helpers => honestHelpers params oStmt xval
    have hmid : ((stmtAfter, oStmtAfter), ()) ∈ logupMidRelation F n M params := by
      simpa [stmtAfter, oStmtAfter] using
        (honestOuterOutput_mem_logupMidRelation F n M params stmt oStmt xval zlam hIn
          hNoTablePoles)
    simp only [OStmtAfterOuter, OStmtIn, MultiplicityMessage, HelperMessages]
    constructor
    · convert hmid using 2
    · rfl
  · exact hGoodProbability

/-! ## Sumcheck Phase Completeness

The embedded sumcheck phase reuses ArkLib's generic perfect completeness theorem through the LogUp
context lens.  The lens proof shows that the projected sumcheck statement is the zero-sum instance
and that a valid final sumcheck claim lifts back to the retained LogUp data. -/

/-- Lens-completeness for the LogUp→Sumcheck lens: `proj` builds the zero-sum instance, and `lift`
retains the outer LogUp data together with sumcheck's final valid point claim. -/
instance logupSumcheckLensComplete :
    (logupSumcheckContextLens F n M params).toContext.IsComplete
      (logupMidRelation F n M params)
      (Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F) 0)
      (logupAfterSumcheckRelation F n M params)
      (Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F)
        (Fin.last n))
      ((logupConcreteSumcheckOracleReduction oSpec F n M params).toReduction.compatContext
        (logupSumcheckContextLens F n M params).toContext) where
  proj_complete := by
    rintro ⟨stmt, oStmt⟩ ⟨⟩ h
    exact logupSumcheckRelationInput_of_zero F n M params h
  lift_complete := by
    intro outerStmt outerWit innerStmtOut innerWitOut hCompat _ hRelOut
    have hOStmt :
        innerStmtOut.2 = logupSumcheckOracleStmt F n M params outerStmt.1 outerStmt.2 := by
      simp only [Reduction.compatContext, Function.comp_apply, ProtocolSpec.ChallengeIdx,
        ProtocolSpec.Challenge, OStmtAfterOuter, OStmtIn, MultiplicityMessage, HelperMessages,
        Set.mem_image, OptionT.mem_support_iff, Prod.exists, exists_and_right,
        exists_eq_right] at hCompat
      rcases hCompat with ⟨td, vOut, verOStmt, hRun⟩
      have hProver := reduction_run_prover_mem
        ((logupConcreteSumcheckOracleReduction oSpec F n M params).toReduction)
        ((logupSumcheckContextLens F n M params).toContext.proj (outerStmt, outerWit)).1
        ((logupSumcheckContextLens F n M params).toContext.proj (outerStmt, outerWit)).2
        td innerStmtOut innerWitOut (vOut, verOStmt) hRun
      have hPres := Sumcheck.Spec.prover_preserves_oracleStmt F
        (logupSumcheckDegree M params) (booleanDomain F) n oSpec
        ((logupSumcheckContextLens F n M params).toContext.proj (outerStmt, outerWit)).1
        innerStmtOut td hProver
      simpa [logupSumcheckContextLens, logupSumcheckExecutableContextLens,
        logupSumcheckExecutableStatementLens] using hPres
    cases innerWitOut
    have hPair :
        (innerStmtOut.1, logupSumcheckOracleStmt F n M params outerStmt.1 outerStmt.2) =
          innerStmtOut := by
      cases innerStmtOut
      simpa using hOStmt.symm
    simpa [logupSumcheckContextLens, logupSumcheckExecutableContextLens,
      logupSumcheckExecutableStatementLens, logupAfterSumcheckRelation, hPair] using hRelOut

omit [Fintype F] in
/-- Completeness of the embedded sumcheck phase: it carries `logupMidRelation` to the retained
final sumcheck claim with no extra error, by reusing the generic sumcheck's perfect completeness
through the LogUp-to-Sumcheck context lens. -/
theorem logupSumcheckPhaseCompleteness :
    (sumcheckOracleReduction oSpec F n M params).completeness init impl
      (logupMidRelation F n M params) (logupAfterSumcheckRelation F n M params) 0 :=
  OracleReduction.liftContext_perfectCompleteness
    (lens := logupSumcheckExecutableContextLens F n M params)
    (output := logupSumcheckLiftContextOutput oSpec F n M params)
    (lensComplete := logupSumcheckLensComplete oSpec F n M params)
    (Sumcheck.Spec.oracleReduction_perfectCompleteness
      F (logupSumcheckDegree M params) (booleanDomain F) n oSpec)


/-! ## Final-Check Phase Completeness

The final check is deterministic.  If the retained post-sumcheck relation is valid, the verifier's
oracle queries reconstruct exactly the value of `logupQPolynomial` at the final sumcheck point, so
the guard accepts with probability one. -/

omit [Fintype F] [SampleableType F] in
/-- Completeness of the final LogUp point check: once sumcheck's final claim is valid for the
retained LogUp polynomial, the verifier's oracle queries reconstruct the same value. -/
theorem finalCheckCompleteness :
    (finalCheckOracleReduction oSpec F n M params).completeness init impl
      (logupAfterSumcheckRelation F n M params) outputRelation 0 := by
  unfold OracleReduction.completeness Reduction.completeness
  rintro ⟨stmt, oStmt⟩ ⟨⟩ hRel
  have hExpected :
      MvPolynomial.eval stmt.finalClaim.challenges
          (logupQPolynomial (params.group) (oStmt (.input .table)).1
            (fun i => (oStmt (.input (.column i))).1) (oStmt .multiplicity).1
            (fun k => (oStmt .helpers k).1) stmt.outer.xChallenge stmt.outer.zChallenge
            stmt.outer.batchingScalars) =
        stmt.finalClaim.target := by
    change MvPolynomial.eval (fun i : Fin n => stmt.finalClaim.challenges i)
        (logupQPolynomial (params.group) (oStmt (.input .table)).1
          (fun i => (oStmt (.input (.column i))).1) (oStmt .multiplicity).1
          (fun k => (oStmt .helpers k).1) stmt.outer.xChallenge stmt.outer.zChallenge
          stmt.outer.batchingScalars) =
      stmt.finalClaim.target
    have hRel' :
        ((stmt.finalClaim, logupSumcheckOracleStmt F n M params stmt.outer oStmt), ()) ∈
          Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F)
            (Fin.last n) := by
      simpa [logupAfterSumcheckRelation] using hRel
    have hEval :=
      (Sumcheck.Spec.relationRound_last_iff
        (R := F) (n := n) (deg := logupSumcheckDegree M params) (D := booleanDomain F)
        (stmt := stmt.finalClaim)
        (polyOracle := logupSumcheckOracleStmt F n M params stmt.outer oStmt)).1 hRel'
    simpa [logupSumcheckOracleStmt, logupSumcheckPolynomial] using hEval
  have hGuard :
      qAtPoint (params.group) stmt.outer.xChallenge stmt.outer.zChallenge
          stmt.finalClaim.challenges stmt.outer.batchingScalars
          (MvPolynomial.eval stmt.finalClaim.challenges (oStmt .multiplicity).1)
          (MvPolynomial.eval stmt.finalClaim.challenges (oStmt (.input .table)).1)
          (fun i => MvPolynomial.eval stmt.finalClaim.challenges (oStmt (.input (.column i))).1)
          (fun k => MvPolynomial.eval stmt.finalClaim.challenges (oStmt .helpers k).1) =
        stmt.finalClaim.target := by
    rw [← hExpected]
    exact (logupQPolynomial_eval_point (params.group) (oStmt (.input .table)).1
      (fun i => (oStmt (.input (.column i))).1) (oStmt .multiplicity).1
      (fun k => (oStmt .helpers k).1) stmt.outer.xChallenge stmt.outer.zChallenge
      stmt.finalClaim.challenges stmt.outer.batchingScalars).symm
  let qImpl :
      QueryImpl
        (oSpec + ([OStmtAfterOuter F n M params]ₒ + [finalCheckPSpec.Message]ₒ))
        (OracleComp oSpec) :=
    OracleInterface.simOracle2 (T₁ := OStmtAfterOuter F n M params)
      (T₂ := finalCheckPSpec.Message) oSpec oStmt
      (fun i : finalCheckPSpec.MessageIdx => Fin.elim0 i)
  have hquery :
      ∀ (i : OuterOracleIdx M)
        (q : (instOStmtAfterOuterOracleInterface (F := F) (n := n) (params := params) i).Query),
        simulateQ qImpl ((finalCheckQuery oSpec F n M params i q).run) =
          (pure (some ((instOStmtAfterOuterOracleInterface
            (F := F) (n := n) (params := params) i).answer (oStmt i) q)) :
            OracleComp oSpec _) := by
    intro i q
    simp only [finalCheckQuery, OptionT.run_mk, simulateQ_map, qImpl,
      OracleInterface.simOracle2, QueryImpl.addLift_def, OracleInterface.answer]
    change some <$> id <$>
        (pure (ReaderT.run (OracleInterface.toOC.impl q) (oStmt i)) :
          OracleComp oSpec _) =
      (pure (some (ReaderT.run (OracleInterface.toOC.impl q) (oStmt i))) :
        OracleComp oSpec _)
    simp
  have hVerify :
      simulateQ qImpl
          ((finalCheckVerifier oSpec F n M params).verify stmt (fun i => Fin.elim0 i)).run =
        (pure (some ()) : OracleComp oSpec (Option StmtOut)) := by
    simp only [finalCheckVerifier, OptionT.run_bind, OptionT.run_pure]
    erw [simulateQ_bind]
    rw [hquery .multiplicity stmt.finalClaim.challenges]
    simp only [pure_bind, Option.elim_some]
    erw [simulateQ_bind]
    rw [hquery (.input .table) stmt.finalClaim.challenges]
    simp only [pure_bind, Option.elim_some]
    let colValue := fun i : Fin M =>
      MvPolynomial.eval stmt.finalClaim.challenges (oStmt (.input (.column i))).1
    have hcolAnswer : ∀ i : Fin M,
        ReaderT.run (OracleInterface.toOC.impl stmt.finalClaim.challenges)
            (oStmt (.input (.column i))) =
          colValue i := fun _ => rfl
    have hcols := simulateQ_optionT_vector_mapM_pure qImpl
      (fun i : Fin M =>
        finalCheckQuery oSpec F n M params (.input (.column i)) stmt.finalClaim.challenges)
      colValue (Vector.finRange M) (by
        intro i
        change simulateQ qImpl
            ((finalCheckQuery oSpec F n M params (.input (.column i))
              stmt.finalClaim.challenges).run) =
          (pure (some (colValue i)) : OracleComp oSpec (Option F))
        rw [hquery (.input (.column i)) stmt.finalClaim.challenges]
        change (pure (some
          (ReaderT.run (OracleInterface.toOC.impl stmt.finalClaim.challenges)
            (oStmt (.input (.column i)))))) =
          (pure (some (colValue i)) : OracleComp oSpec (Option F))
        rw [hcolAnswer])
    erw [simulateQ_option_elimM]
    erw [hcols]
    simp only [pure_bind, Option.elimM, Option.elim_some]
    let helperValue := fun k : Fin params.numGroups =>
      MvPolynomial.eval stmt.finalClaim.challenges (oStmt .helpers k).1
    have hhelperAnswer : ∀ k : Fin params.numGroups,
        ReaderT.run (OracleInterface.toOC.impl
            (show OracleInterface.Query (OStmtAfterOuter F n M params .helpers) from
              ⟨k, stmt.finalClaim.challenges⟩))
            (oStmt .helpers) =
          helperValue k := fun _ => rfl
    have hhelpers := simulateQ_optionT_vector_mapM_pure qImpl
      (fun k : Fin params.numGroups =>
        finalCheckQuery oSpec F n M params .helpers ⟨k, stmt.finalClaim.challenges⟩)
      helperValue (Vector.finRange params.numGroups) (by
        intro k
        change simulateQ qImpl
            ((finalCheckQuery oSpec F n M params .helpers
              ⟨k, stmt.finalClaim.challenges⟩).run) =
          (pure (some (helperValue k)) : OracleComp oSpec (Option F))
        rw [hquery .helpers ⟨k, stmt.finalClaim.challenges⟩]
        change (pure (some
          (ReaderT.run (OracleInterface.toOC.impl
            (show OracleInterface.Query (OStmtAfterOuter F n M params .helpers) from
              ⟨k, stmt.finalClaim.challenges⟩))
            (oStmt .helpers)))) =
          (pure (some (helperValue k)) : OracleComp oSpec (Option F))
        exact congrArg (fun x => pure (some x)) (hhelperAnswer k))
    erw [simulateQ_option_elimM]
    erw [hhelpers]
    simp only [pure_bind, Option.elimM, Option.elim_some]
    have hmultAnswer :
        ReaderT.run (OracleInterface.toOC.impl stmt.finalClaim.challenges)
            (oStmt .multiplicity) =
          MvPolynomial.eval stmt.finalClaim.challenges (oStmt .multiplicity).1 := rfl
    have htableAnswer :
        ReaderT.run (OracleInterface.toOC.impl stmt.finalClaim.challenges)
            (oStmt (.input .table)) =
          MvPolynomial.eval stmt.finalClaim.challenges (oStmt (.input .table)).1 := rfl
    have hGuard' :
        qAtPoint (params.group) stmt.outer.xChallenge stmt.outer.zChallenge
            stmt.finalClaim.challenges stmt.outer.batchingScalars
            (ReaderT.run (OracleInterface.toOC.impl stmt.finalClaim.challenges)
              (oStmt .multiplicity))
            (ReaderT.run (OracleInterface.toOC.impl stmt.finalClaim.challenges)
              (oStmt (.input .table)))
            colValue
            helperValue =
          stmt.finalClaim.target := by
      simpa [hmultAnswer, htableAnswer, colValue, helperValue] using hGuard
    have hGuardAnswer :
        qAtPoint (params.group) stmt.outer.xChallenge stmt.outer.zChallenge
            stmt.finalClaim.challenges stmt.outer.batchingScalars
            (OracleInterface.answer (oStmt .multiplicity) stmt.finalClaim.challenges)
            (OracleInterface.answer (oStmt (.input .table)) stmt.finalClaim.challenges)
            colValue
            helperValue =
          stmt.finalClaim.target := by
      simpa [OracleInterface.answer] using hGuard'
    erw [simulateQ_option_elimM]
    simp [guard, hGuardAnswer, Option.elimM]
  have hVerifyDefault :
      simulateQ
          (OracleInterface.simOracle2 oSpec oStmt
            (ProtocolSpec.FullTranscript.messages (default : finalCheckPSpec.FullTranscript)))
          (((finalCheckVerifier oSpec F n M params).verify stmt
            (ProtocolSpec.FullTranscript.challenges
              (default : finalCheckPSpec.FullTranscript))).run) =
        (pure (some ()) : OracleComp oSpec (Option StmtOut)) := by
    change simulateQ qImpl
        (((finalCheckVerifier oSpec F n M params).verify stmt (fun i => Fin.elim0 i)).run) =
      (pure (some ()) : OracleComp oSpec (Option StmtOut))
    exact hVerify
  have hrun :
      (finalCheckOracleReduction oSpec F n M params).toReduction.run (stmt, oStmt) () =
        (pure ((default, ((), fun i => Fin.elim0 i), ()), ((), fun i => Fin.elim0 i)) :
          OptionT (OracleComp _) _) := by
    simp only [finalCheckPSpec, ProtocolSpec.ChallengeIdx, ProtocolSpec.Challenge, StmtOut,
      OutputOracleIdx, OStmtOut, Reduction.run, Prover.run, Fin.reduceLast, OStmtAfterOuter,
      OStmtIn, MultiplicityMessage, HelperMessages, finalCheckOracleReduction, finalCheckProver,
      Nat.reduceAdd, Fin.isValue, ProtocolSpec.MessageIdx, ProtocolSpec.Message,
      OracleReduction.toReduction, OracleVerifier.toVerifier, Prover.runToRound, Fin.induction_zero,
      liftM_pure, bind_pure_comp, map_pure, Verifier.run, pure_bind]
    erw [hVerifyDefault]
    simp only [StmtOut, OptionT.run_mk, liftM_pure, Fin.isValue, pure_bind, Option.map_some,
      Option.getM_some, map_pure, OracleVerifier.materializeOutput,
      OracleVerifier.materializeOutputOracle, finalCheckVerifier]
    congr
    funext i
    exact Fin.elim0 i
  simp only [ENNReal.coe_zero, tsub_zero]
  rw [hrun]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _ hmem
    change none ∈ _root_.support
      (StateT.run' (simulateQ _
        (pure (some
          ((default, ((), fun i => Fin.elim0 i), ()), ((), fun i => Fin.elim0 i))) :
            OracleComp _ _)) s) at hmem
    rw [simulateQ_pure] at hmem
    change none ∈ _root_.support
      (Prod.fst <$> (pure (some
        ((default, ((), fun i => Fin.elim0 i), ()), ((), fun i => Fin.elim0 i))) :
          StateT σ ProbComp _).run s) at hmem
    rw [StateT.run_pure] at hmem
    simp [map_pure] at hmem
  · intro out hout
    rw [OptionT.mem_support_iff] at hout
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hout
    obtain ⟨s, -, hout⟩ := hout
    change some out ∈ _root_.support
      (StateT.run' (simulateQ _
        (pure (some
          ((default, ((), fun i => Fin.elim0 i), ()), ((), fun i => Fin.elim0 i))) :
            OracleComp _ _)) s) at hout
    rw [simulateQ_pure] at hout
    change some out ∈ _root_.support
      (Prod.fst <$> (pure (some
        ((default, ((), fun i => Fin.elim0 i), ()), ((), fun i => Fin.elim0 i))) :
          StateT σ ProbComp _).run s) at hout
    rw [StateT.run_pure] at hout
    simp only [StmtOut, OutputOracleIdx, OStmtOut, map_pure, support_pure, Set.mem_singleton_iff,
      Option.some.injEq] at hout
    cases hout
    exact ⟨Set.mem_univ _, rfl⟩

/-! ## Composed LogUp Completeness

The full oracle reduction is the sequential composition of the outer phase, embedded sumcheck, and
final check.  Completeness follows by composing the three phase completeness bounds; only the outer
phase contributes the current pole-sampling error. -/

/-- Main ArkLib completeness theorem for LogUp Protocol 2. -/
theorem logup_completeness :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) := by
  let _ : Inhabited F := ⟨0⟩
  have hOuterSumcheck := OracleReduction.append_completeness
    (outerOracleReduction oSpec F n M params)
    (sumcheckOracleReduction oSpec F n M params)
    (logup_outer_completeness oSpec F n M params init impl)
    (logupSumcheckPhaseCompleteness oSpec F n M params init impl)
  have hFull := OracleReduction.append_completeness
    ((outerOracleReduction oSpec F n M params).append
      (sumcheckOracleReduction oSpec F n M params))
    (finalCheckOracleReduction oSpec F n M params)
    hOuterSumcheck
    (finalCheckCompleteness oSpec F n M params init impl)
  let _ : ∀ i, SampleableType
      (((outerPSpec F n params ++ₚ Sumcheck.Spec.pSpec F (logupSumcheckDegree M params) n)
        ++ₚ finalCheckPSpec).Challenge i) :=
    fun i => ProtocolSpec.instSampleableTypeChallengeAppend i
  change ((((outerOracleReduction oSpec F n M params).append
      (sumcheckOracleReduction oSpec F n M params)).append
      (finalCheckOracleReduction oSpec F n M params)).completeness init impl
        (inputRelation F n M) outputRelation (logupCompletenessError F n))
  simpa only [add_zero] using hFull

end Completeness

end Logup
