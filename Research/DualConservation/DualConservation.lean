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

open scoped BigOperators
open MeasureTheory Set

section FiniteCharging

variable {ι Ω : Type*} [Fintype ι]

/-- Summing locally charged failure mass preserves a root alpha budget. -/
theorem finite_alpha_charging
    (charged allocated : ι → ℝ≥0∞) (rootAlpha : ℝ≥0∞)
    (hLocal : ∀ i, charged i ≤ allocated i)
    (hBudget : (∑ i, allocated i) ≤ rootAlpha) :
    (∑ i, charged i) ≤ rootAlpha := by
  exact (Finset.sum_le_sum fun i _ => hLocal i).trans hBudget

/--
Arbitrarily dependent first-failure events compose under an additive alpha
budget. `firstFailure i` should denote the event that commit `i` is the first
certificate failure on its execution history.
-/
theorem adaptive_global_failure_bound
    [MeasurableSpace Ω]
    (μ : Measure Ω)
    (firstFailure : ι → Set Ω)
    (allocatedAlpha : ι → ℝ≥0∞)
    (rootAlpha : ℝ≥0∞)
    (hLocal : ∀ i, μ (firstFailure i) ≤ allocatedAlpha i)
    (hBudget : (∑ i, allocatedAlpha i) ≤ rootAlpha) :
    μ (⋃ i, firstFailure i) ≤ rootAlpha := by
  calc
    μ (⋃ i, firstFailure i) ≤ ∑ i, μ (firstFailure i) :=
      measure_iUnion_fintype_le μ firstFailure
    _ ≤ ∑ i, allocatedAlpha i := Finset.sum_le_sum fun i _ => hLocal i
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
    (allocatedAlpha : ι → ℝ≥0∞)
    (rootReserve : ℕ)
    (rootAlpha : ℝ≥0∞)
    (hReserve : (∑ i, reserve i) ≤ rootReserve)
    (hLocal : ∀ i, μ {ω | reserve i < loss i ω} ≤ allocatedAlpha i)
    (hAlpha : (∑ i, allocatedAlpha i) ≤ rootAlpha) :
    μ {ω | rootReserve < ∑ i, loss i ω} ≤ rootAlpha := by
  calc
    μ {ω | rootReserve < ∑ i, loss i ω} ≤
        μ (⋃ i, {ω | reserve i < loss i ω}) :=
      measure_mono (aggregate_exceedance_subset_local_failure loss reserve rootReserve hReserve)
    _ ≤ ∑ i, μ {ω | reserve i < loss i ω} :=
      measure_iUnion_fintype_le μ fun i => {ω | reserve i < loss i ω}
    _ ≤ ∑ i, allocatedAlpha i := Finset.sum_le_sum fun i _ => hLocal i
    _ ≤ rootAlpha := hAlpha

end FiniteCharging

section DualLedger

variable {ι : Type*} [Fintype ι]

/-- Deterministic and statistical capabilities are conserved componentwise. -/
theorem dual_accounting
    (usedReserve allocatedReserve : ι → ℕ)
    (chargedAlpha allocatedAlpha : ι → ℝ≥0∞)
    (rootReserve : ℕ)
    (rootAlpha : ℝ≥0∞)
    (hReserveLocal : ∀ i, usedReserve i ≤ allocatedReserve i)
    (hAlphaLocal : ∀ i, chargedAlpha i ≤ allocatedAlpha i)
    (hReserveBudget : (∑ i, allocatedReserve i) ≤ rootReserve)
    (hAlphaBudget : (∑ i, allocatedAlpha i) ≤ rootAlpha) :
    (∑ i, usedReserve i) ≤ rootReserve ∧
      (∑ i, chargedAlpha i) ≤ rootAlpha := by
  constructor
  · exact (Finset.sum_le_sum fun i _ => hReserveLocal i).trans hReserveBudget
  · exact (Finset.sum_le_sum fun i _ => hAlphaLocal i).trans hAlphaBudget

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
      simp [WellFormed, leafReserve, leafAlpha, root]
  | fork budget left right ihLeft ihRight =>
      rcases h with ⟨hReserve, hAlpha, hLeft, hRight⟩
      have leftBound := ihLeft hLeft
      have rightBound := ihRight hRight
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

section BurnLaw

/--
`free` alpha may be bound to an unobserved action. Once the action is observed,
its alpha moves to `burned`. Only pending, unobserved alpha may be cancelled.
-/
structure AlphaLedger where
  free : ℕ
  pending : ℕ
  burned : ℕ
  deriving DecidableEq, Repr

namespace AlphaLedger

/-- Total alpha mass represented by the ledger. -/
def total (s : AlphaLedger) : ℕ := s.free + s.pending + s.burned

/-- Bind alpha before observing an action outcome. -/
def bind (s : AlphaLedger) (amount : ℕ) (h : amount ≤ s.free) : AlphaLedger :=
  { free := s.free - amount
    pending := s.pending + amount
    burned := s.burned }

/-- Cancel an unobserved action and return its pending alpha. -/
def cancel (s : AlphaLedger) (amount : ℕ) (h : amount ≤ s.pending) : AlphaLedger :=
  { free := s.free + amount
    pending := s.pending - amount
    burned := s.burned }

/-- Observe an action outcome, irreversibly burning its bound alpha. -/
def observe (s : AlphaLedger) (amount : ℕ) (h : amount ≤ s.pending) : AlphaLedger :=
  { free := s.free
    pending := s.pending - amount
    burned := s.burned + amount }

@[simp] theorem total_bind (s : AlphaLedger) (amount : ℕ) (h : amount ≤ s.free) :
    (s.bind amount h).total = s.total := by
  simp [bind, total]
  omega

@[simp] theorem total_cancel (s : AlphaLedger) (amount : ℕ) (h : amount ≤ s.pending) :
    (s.cancel amount h).total = s.total := by
  simp [cancel, total]
  omega

@[simp] theorem total_observe (s : AlphaLedger) (amount : ℕ) (h : amount ≤ s.pending) :
    (s.observe amount h).total = s.total := by
  simp [observe, total]
  omega

end AlphaLedger

/-- Trusted transitions. There is intentionally no transition from burned to free. -/
inductive AlphaStep : AlphaLedger → AlphaLedger → Prop
  | bind (s : AlphaLedger) (amount : ℕ) (h : amount ≤ s.free) :
      AlphaStep s (s.bind amount h)
  | cancel (s : AlphaLedger) (amount : ℕ) (h : amount ≤ s.pending) :
      AlphaStep s (s.cancel amount h)
  | observe (s : AlphaLedger) (amount : ℕ) (h : amount ≤ s.pending) :
      AlphaStep s (s.observe amount h)

namespace AlphaStep

/-- Every trusted transition conserves total alpha mass. -/
theorem total_eq {s t : AlphaLedger} (h : AlphaStep s t) : t.total = s.total := by
  cases h with
  | bind s amount h => exact AlphaLedger.total_bind s amount h
  | cancel s amount h => exact AlphaLedger.total_cancel s amount h
  | observe s amount h => exact AlphaLedger.total_observe s amount h

/-- Burned confidence is monotone under every trusted transition. -/
theorem burned_mono {s t : AlphaLedger} (h : AlphaStep s t) : s.burned ≤ t.burned := by
  cases h <;> simp [AlphaLedger.bind, AlphaLedger.cancel, AlphaLedger.observe]

end AlphaStep

/-- Reflexive-transitive closure of trusted ledger transitions. -/
inductive AlphaReachable : AlphaLedger → AlphaLedger → Prop
  | refl (s : AlphaLedger) : AlphaReachable s s
  | tail {s t u : AlphaLedger} :
      AlphaReachable s t → AlphaStep t u → AlphaReachable s u

namespace AlphaReachable

/-- Total alpha mass is invariant along every valid execution. -/
theorem total_eq {s t : AlphaLedger} (h : AlphaReachable s t) : t.total = s.total := by
  induction h with
  | refl s => rfl
  | tail hReach hStep ih => exact hStep.total_eq.trans ih

/--
Confidence burn law: once alpha is burned, no valid future execution can make
it unburned. Successful observation is not a refund operation.
-/
theorem burned_mono {s t : AlphaLedger} (h : AlphaReachable s t) :
    s.burned ≤ t.burned := by
  induction h with
  | refl s => exact le_rfl
  | tail hReach hStep ih => exact ih.trans hStep.burned_mono

/-- Alpha burned by one observation remains burned in every reachable state. -/
theorem observed_irreversible
    (s u : AlphaLedger)
    (amount : ℕ)
    (hPending : amount ≤ s.pending)
    (hReach : AlphaReachable (s.observe amount hPending) u) :
    s.burned + amount ≤ u.burned := by
  simpa [AlphaLedger.observe] using hReach.burned_mono

end AlphaReachable

end BurnLaw

section ConcreteAudit

/-- Twenty copies of a five-percent allowance consume one hundred percent. -/
example : 20 * 50_000 = 1_000_000 := by norm_num

/-- An equal split of a five-percent root allowance across twenty agents. -/
example : 20 * 2_500 = 50_000 := by norm_num

end ConcreteAudit

end DualConservation
