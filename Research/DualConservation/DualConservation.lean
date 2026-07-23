import Mathlib

/-!
# Dual conservation for recursive agent delegation

This file formalizes the accounting kernel behind a proposed agentic-systems
protocol. A root agent owns two linear capabilities:

* a deterministic reserve budget; and
* a statistical miscoverage budget (alpha).

Both must be split, never copied, across committed descendants. The probability
theorems use outer-measure subadditivity and therefore make no independence
assumption.
-/

namespace DualConservation

open scoped BigOperators ENNReal
open MeasureTheory Set

section FiniteCharging

variable {ι Ω : Type*} [Fintype ι]

/-- Summing locally charged failure mass preserves a root alpha budget. -/
theorem finite_alpha_charging
    (charged allocation : ι → ℝ≥0∞) (rootAlpha : ℝ≥0∞)
    (hLocal : ∀ i, charged i ≤ allocation i)
    (hBudget : (∑ i, allocation i) ≤ rootAlpha) :
    (∑ i, charged i) ≤ rootAlpha := by
  exact (Finset.sum_le_sum fun i _ => hLocal i).trans hBudget

/--
Arbitrarily dependent first-failure events compose under an additive alpha
budget. `firstFailure i` should denote the event that commit `i` is the first
certificate failure on its execution history.
-/
theorem first_failure_union_bound
    [MeasurableSpace Ω]
    (μ : Measure Ω)
    (firstFailure : ι → Set Ω)
    (alphaAllocation : ι → ℝ≥0∞)
    (rootAlpha : ℝ≥0∞)
    (hLocal : ∀ i, μ (firstFailure i) ≤ alphaAllocation i)
    (hBudget : (∑ i, alphaAllocation i) ≤ rootAlpha) :
    μ (⋃ i, firstFailure i) ≤ rootAlpha := by
  calc
    μ (⋃ i, firstFailure i) ≤ ∑ i, μ (firstFailure i) :=
      measure_iUnion_fintype_le μ firstFailure
    _ ≤ ∑ i, alphaAllocation i := Finset.sum_le_sum fun i _ => hLocal i
    _ ≤ rootAlpha := hBudget

/--
If total deterministic reserves fit the root budget, then exceeding the root
budget implies at least one local reserve breach.
-/
theorem aggregate_exceedance_subset_local_failure
    (loss : ι → Ω → ℕ)
    (reserve : ι → ℕ)
    (rootReserve : ℕ)
    (hReserve : (∑ i, reserve i) ≤ rootReserve) :
    {ω | rootReserve < ∑ i, loss i ω} ⊆
      ⋃ i, {ω | reserve i < loss i ω} := by
  intro ω hExceed
  by_contra hNoLocalFailure
  have hLocal : ∀ i, loss i ω ≤ reserve i := by
    intro i
    by_contra hBreach
    have hStrict : reserve i < loss i ω := Nat.lt_of_not_ge hBreach
    exact hNoLocalFailure (Set.mem_iUnion.2 ⟨i, hStrict⟩)
  have hSum : (∑ i, loss i ω) ≤ ∑ i, reserve i :=
    Finset.sum_le_sum fun i _ => hLocal i
  exact (not_lt_of_ge (hSum.trans hReserve)) hExceed

/--
Dual global guarantee: additive reserve allocation plus additive alpha
allocation bounds the probability of aggregate loss exceeding the root reserve.
No independence assumption is used.
-/
theorem dual_conservation_probability
    [MeasurableSpace Ω]
    (μ : Measure Ω)
    (loss : ι → Ω → ℕ)
    (reserve : ι → ℕ)
    (alphaAllocation : ι → ℝ≥0∞)
    (rootReserve : ℕ)
    (rootAlpha : ℝ≥0∞)
    (hReserve : (∑ i, reserve i) ≤ rootReserve)
    (hLocal : ∀ i, μ {ω | reserve i < loss i ω} ≤ alphaAllocation i)
    (hAlpha : (∑ i, alphaAllocation i) ≤ rootAlpha) :
    μ {ω | rootReserve < ∑ i, loss i ω} ≤ rootAlpha := by
  calc
    μ {ω | rootReserve < ∑ i, loss i ω} ≤
        μ (⋃ i, {ω | reserve i < loss i ω}) :=
      measure_mono (aggregate_exceedance_subset_local_failure loss reserve rootReserve hReserve)
    _ ≤ ∑ i, μ {ω | reserve i < loss i ω} :=
      measure_iUnion_fintype_le μ fun i => {ω | reserve i < loss i ω}
    _ ≤ ∑ i, alphaAllocation i := Finset.sum_le_sum fun i _ => hLocal i
    _ ≤ rootAlpha := hAlpha

end FiniteCharging

section DualLedger

variable {ι : Type*} [Fintype ι]

/-- Deterministic and statistical capabilities are conserved componentwise. -/
theorem dual_accounting
    (usedReserve reserveAllocation : ι → ℕ)
    (chargedAlpha alphaAllocation : ι → ℝ≥0∞)
    (rootReserve : ℕ)
    (rootAlpha : ℝ≥0∞)
    (hReserveLocal : ∀ i, usedReserve i ≤ reserveAllocation i)
    (hAlphaLocal : ∀ i, chargedAlpha i ≤ alphaAllocation i)
    (hReserveBudget : (∑ i, reserveAllocation i) ≤ rootReserve)
    (hAlphaBudget : (∑ i, alphaAllocation i) ≤ rootAlpha) :
    (∑ i, usedReserve i) ≤ rootReserve ∧
      (∑ i, chargedAlpha i) ≤ rootAlpha := by
  constructor
  · exact (Finset.sum_le_sum fun i _ => hReserveLocal i).trans hReserveBudget
  · exact (Finset.sum_le_sum fun i _ => hAlphaLocal i).trans hAlphaBudget

/--
The excess failure probability created by refunding a one-shot allowance after
one observed success is exactly `p * (1 - p)`.
-/
theorem two_attempt_refund_inflation_identity (p : ℝ) :
    (1 - (1 - p)^2) - p = p * (1 - p) := by
  ring

/--
Confidence burn law for two independent attempts: for any nontrivial per-attempt
failure probability, treating a successful first attempt as a refund makes the
two-attempt failure probability strictly larger than the original allowance.
-/
theorem two_attempt_refund_unsound
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    p < 1 - (1 - p)^2 := by
  rw [← sub_pos]
  rw [two_attempt_refund_inflation_identity p]
  exact mul_pos hp0 (sub_pos.mpr hp1)

/-- A positive confidence budget cannot be copied even to two children. -/
theorem binary_confidence_no_cloning (alpha : ℕ) (hAlpha : 0 < alpha) :
    alpha < alpha + alpha := by
  omega

/-- Copying a positive confidence budget to any fleet of at least two exceeds it. -/
theorem fleet_confidence_no_cloning
    (alpha children : ℕ)
    (hAlpha : 0 < alpha)
    (hChildren : 2 ≤ children) :
    alpha < children * alpha := by
  calc
    alpha < 2 * alpha := by omega
    _ ≤ children * alpha := Nat.mul_le_mul_right alpha hChildren

end DualLedger

section RecursiveDelegation

/-- A pair of linear capabilities carried by a delegation node. -/
structure DualBudget where
  reserve : ℕ
  alpha : ℕ
  deriving DecidableEq, Repr

/-- A binary recursive delegation tree. Every fork carries its own budget. -/
inductive DelegationTree where
  | leaf (budget : DualBudget)
  | fork (budget : DualBudget) (left right : DelegationTree)
  deriving Repr

namespace DelegationTree

/-- Budget attached to the root of a delegation tree. -/
def root : DelegationTree → DualBudget
  | .leaf budget => budget
  | .fork budget _ _ => budget

/-- Total reserve delegated to terminal agents. -/
def leafReserve : DelegationTree → ℕ
  | .leaf budget => budget.reserve
  | .fork _ left right => left.leafReserve + right.leafReserve

/-- Total alpha delegated to terminal agents. -/
def leafAlpha : DelegationTree → ℕ
  | .leaf budget => budget.alpha
  | .fork _ left right => left.leafAlpha + right.leafAlpha

/--
Every fork must split, rather than copy, both of its capabilities. This local
condition is enough to imply a global bound over an arbitrarily deep tree.
-/
def WellFormed : DelegationTree → Prop
  | .leaf _ => True
  | .fork budget left right =>
      left.root.reserve + right.root.reserve ≤ budget.reserve ∧
      left.root.alpha + right.root.alpha ≤ budget.alpha ∧
      left.WellFormed ∧ right.WellFormed

/--
Recursive dual-conservation theorem: local split constraints imply that the sum
of all terminal reserve and alpha allocations is bounded by the root budget.
-/
theorem recursive_dual_conservation (tree : DelegationTree)
    (h : tree.WellFormed) :
    tree.leafReserve ≤ tree.root.reserve ∧
      tree.leafAlpha ≤ tree.root.alpha := by
  induction tree with
  | leaf budget =>
      simp [leafReserve, leafAlpha, root]
  | fork budget left right ihLeft ihRight =>
      rcases h with ⟨hReserve, hAlpha, hLeft, hRight⟩
      rcases ihLeft hLeft with ⟨hLeftReserve, hLeftAlpha⟩
      rcases ihRight hRight with ⟨hRightReserve, hRightAlpha⟩
      simp only [leafReserve, leafAlpha, root]
      constructor <;> omega

end DelegationTree

/--
Two independent uses of a positive local failure allowance `p` already exceed
that same global allowance. This is the arithmetic core of the no-refund rule:
a successful observation cannot make the statistical budget reusable.
-/
theorem two_use_confidence_recycling_unsound
    (p : ℝ) (hPositive : 0 < p) (hBelowOne : p < 1) :
    p < 1 - (1 - p) ^ 2 := by
  have hProduct : 0 < p * (1 - p) :=
    mul_pos hPositive (sub_pos.mpr hBelowOne)
  nlinarith

/-- At five percent, two recycled uses have a 9.75 percent failure chance. -/
example : (5 : ℚ) / 100 < 1 - (1 - (5 : ℚ) / 100) ^ 2 := by
  norm_num

end RecursiveDelegation

section BurnLaw

/--
A statistical allocation has four phases:

* `free`: not delegated;
* `pending`: bound but provably unexposed;
* `exposed`: the risk event can already have occurred, but the result has not
  entered control logic; and
* `observed`: the result can influence future choices.

Both `exposed` and `observed` are burned. Only pending, unexposed alpha may be
cancelled into the free pool.
-/
structure AlphaLedger where
  free : ℕ
  pending : ℕ
  exposed : ℕ
  observed : ℕ
  deriving DecidableEq, Repr

namespace AlphaLedger

/-- Total alpha mass represented by the ledger. -/
def total (s : AlphaLedger) : ℕ :=
  s.free + s.pending + s.exposed + s.observed

/-- Alpha that has crossed the risk-exposure boundary. -/
def burned (s : AlphaLedger) : ℕ := s.exposed + s.observed

/-- Bind alpha before an action can create the certified risk event. -/
def bind (s : AlphaLedger) (amount : ℕ) (_h : amount ≤ s.free) : AlphaLedger :=
  { free := s.free - amount
    pending := s.pending + amount
    exposed := s.exposed
    observed := s.observed }

/-- Cancel a provably unexposed action and return its pending alpha. -/
def cancel (s : AlphaLedger) (amount : ℕ) (_h : amount ≤ s.pending) : AlphaLedger :=
  { free := s.free + amount
    pending := s.pending - amount
    exposed := s.exposed
    observed := s.observed }

/-- Commit the risk exposure, irreversibly burning bound alpha. -/
def expose (s : AlphaLedger) (amount : ℕ) (_h : amount ≤ s.pending) : AlphaLedger :=
  { free := s.free
    pending := s.pending - amount
    exposed := s.exposed + amount
    observed := s.observed }

/-- Reveal an already-exposed outcome to control logic. -/
def observe (s : AlphaLedger) (amount : ℕ) (_h : amount ≤ s.exposed) : AlphaLedger :=
  { free := s.free
    pending := s.pending
    exposed := s.exposed - amount
    observed := s.observed + amount }

@[simp] theorem total_bind (s : AlphaLedger) (amount : ℕ) (h : amount ≤ s.free) :
    (s.bind amount h).total = s.total := by
  simp [bind, total]
  omega

@[simp] theorem total_cancel (s : AlphaLedger) (amount : ℕ) (h : amount ≤ s.pending) :
    (s.cancel amount h).total = s.total := by
  simp [cancel, total]
  omega

@[simp] theorem total_expose (s : AlphaLedger) (amount : ℕ) (h : amount ≤ s.pending) :
    (s.expose amount h).total = s.total := by
  simp [expose, total]
  omega

@[simp] theorem total_observe (s : AlphaLedger) (amount : ℕ) (h : amount ≤ s.exposed) :
    (s.observe amount h).total = s.total := by
  simp [observe, total]
  omega

@[simp] theorem burned_bind (s : AlphaLedger) (amount : ℕ) (h : amount ≤ s.free) :
    (s.bind amount h).burned = s.burned := by
  simp [bind, burned]

@[simp] theorem burned_cancel (s : AlphaLedger) (amount : ℕ) (h : amount ≤ s.pending) :
    (s.cancel amount h).burned = s.burned := by
  simp [cancel, burned]

@[simp] theorem burned_expose (s : AlphaLedger) (amount : ℕ) (h : amount ≤ s.pending) :
    (s.expose amount h).burned = s.burned + amount := by
  simp [expose, burned]
  omega

@[simp] theorem burned_observe (s : AlphaLedger) (amount : ℕ) (h : amount ≤ s.exposed) :
    (s.observe amount h).burned = s.burned := by
  simp [observe, burned]
  omega

end AlphaLedger

/-- Trusted transitions. There is intentionally no burned-to-free transition. -/
inductive AlphaStep : AlphaLedger → AlphaLedger → Prop
  | bind (s : AlphaLedger) (amount : ℕ) (h : amount ≤ s.free) :
      AlphaStep s (s.bind amount h)
  | cancel (s : AlphaLedger) (amount : ℕ) (h : amount ≤ s.pending) :
      AlphaStep s (s.cancel amount h)
  | expose (s : AlphaLedger) (amount : ℕ) (h : amount ≤ s.pending) :
      AlphaStep s (s.expose amount h)
  | observe (s : AlphaLedger) (amount : ℕ) (h : amount ≤ s.exposed) :
      AlphaStep s (s.observe amount h)

namespace AlphaStep

/-- Every trusted transition conserves total alpha mass. -/
theorem total_eq {s t : AlphaLedger} (h : AlphaStep s t) : t.total = s.total := by
  cases h with
  | bind amount h => exact AlphaLedger.total_bind _ amount h
  | cancel amount h => exact AlphaLedger.total_cancel _ amount h
  | expose amount h => exact AlphaLedger.total_expose _ amount h
  | observe amount h => exact AlphaLedger.total_observe _ amount h

/-- Burned confidence is monotone under every trusted transition. -/
theorem burned_mono {s t : AlphaLedger} (h : AlphaStep s t) :
    s.burned ≤ t.burned := by
  cases h with
  | bind amount h => simp
  | cancel amount h => simp
  | expose amount h => simp
  | observe amount h => simp

/-- The amount already observed by control logic is monotone. -/
theorem observed_mono {s t : AlphaLedger} (h : AlphaStep s t) :
    s.observed ≤ t.observed := by
  cases h <;> simp [AlphaLedger.bind, AlphaLedger.cancel,
    AlphaLedger.expose, AlphaLedger.observe]

end AlphaStep

/-- Reflexive-transitive closure of trusted ledger transitions. -/
inductive AlphaReachable : AlphaLedger → AlphaLedger → Prop
  | refl (s : AlphaLedger) : AlphaReachable s s
  | tail {s t u : AlphaLedger} :
      AlphaReachable s t → AlphaStep t u → AlphaReachable s u

namespace AlphaReachable

/-- Total alpha mass is invariant along every valid execution. -/
theorem total_eq {s t : AlphaLedger} (h : AlphaReachable s t) :
    t.total = s.total := by
  induction h with
  | refl => rfl
  | tail hReach hStep ih => exact hStep.total_eq.trans ih

/--
Exposure burn law: once alpha has crossed the risk-exposure boundary, no valid
future execution can return it to free or pending authority.
-/
theorem burned_mono {s t : AlphaLedger} (h : AlphaReachable s t) :
    s.burned ≤ t.burned := by
  induction h with
  | refl => exact le_rfl
  | tail hReach hStep ih => exact ih.trans hStep.burned_mono

/-- Outcomes already visible to control logic cannot become unobserved. -/
theorem observed_mono {s t : AlphaLedger} (h : AlphaReachable s t) :
    s.observed ≤ t.observed := by
  induction h with
  | refl => exact le_rfl
  | tail hReach hStep ih => exact ih.trans hStep.observed_mono

/-- Alpha burned by one exposure remains burned in every reachable state. -/
theorem exposure_irreversible
    (s u : AlphaLedger)
    (amount : ℕ)
    (hPending : amount ≤ s.pending)
    (hReach : AlphaReachable (s.expose amount hPending) u) :
    s.burned + amount ≤ u.burned := by
  simpa using hReach.burned_mono

/-- Alpha made visible by one observation remains observed in every future state. -/
theorem observation_irreversible
    (s u : AlphaLedger)
    (amount : ℕ)
    (hExposed : amount ≤ s.exposed)
    (hReach : AlphaReachable (s.observe amount hExposed) u) :
    s.observed + amount ≤ u.observed := by
  simpa [AlphaLedger.observe] using hReach.observed_mono

end AlphaReachable

end BurnLaw

section ConcreteAudit

/-- Twenty copies of a five-percent allowance consume one hundred percent. -/
example : 20 * 50_000 = 1_000_000 := by norm_num

/-- An equal split of a five-percent root allowance across twenty agents. -/
example : 20 * 2_500 = 50_000 := by norm_num

end ConcreteAudit

end DualConservation
