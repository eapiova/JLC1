{-# OPTIONS --cubical --safe #-}

-- Worked examples of cut elimination, run by the type checker.
--
-- Referee 2 asks for concrete proofs containing applications of the Cut rule
-- that the implemented CutElimination function transforms into cut-free ones.
-- Each example below certifies TWO facts by computation:
--
--   * the input really contains a cut, i.e. its rank is not zero;
--   * the output has rank zero, i.e. it is cut free.
--
-- The second is proved by `refl`, so the type checker is forced to normalise
-- the eliminated proof rather than merely to inspect the contract carried by
-- the second projection.

module S4dot2.CutElimination.Examples where

-- SUMMARY OF WHAT THE TYPE CHECKER OBSERVES HERE.
--
--   example 1, atomic cut between two identity derivations   δ ≡ 0 by refl
--   example 4, non-principal cut, left premise a weakening   δ ≡ 0 by refl
--   example 3, principal cut on a negation                   refl REJECTED
--   example 2, principal cut on a conjunction                refl UNFINISHED
--
-- The whole module elaborates in 0.83 s with a peak residency of 285 MB.  The
-- two negative entries are discussed at their declarations: the first is a
-- definitional conversion that does not hold, and Agda reports it in 3.8 s;
-- the second is a bounded observation, thirty minutes under a 14 GB heap cap.
-- Neither is evidence of nontermination.

open import Cubical.Foundations.Prelude using (_≡_; refl)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using ([])

open import S4dot2.Syntax hiding (_⊢_)
open import S4dot2.System
open import S4dot2.CutElimination.Defs using (δ; degree; isCutFree)
open import S4dot2.CutElimination.CutElimination using (CutElimination)
open import Cubical.Data.Sigma using (Σ; fst)

------------------------------------------------------------------------
-- Example 1 (smoke test): a cut on an atom, between two axioms.
--
--        A^ε ⊢ A^ε        A^ε ⊢ A^ε
--        ------------------------- Cut
--                A^ε ⊢ A^ε

p : Formula
p = Atom 0

cutAxAx : [ p ^ ∅ ] ⊢ [ p ^ ∅ ]
cutAxAx = Cut {A = p} {s = ∅} Ax Ax

-- The input is not cut free: its rank is the degree of the cut formula plus one.
input-has-cut : δ cutAxAx ≡ suc (degree p)
input-has-cut = refl

-- The eliminated proof is cut free, by computation.
output-cut-free : δ (fst (CutElimination cutAxAx)) ≡ 0
output-cut-free = refl

------------------------------------------------------------------------
-- Example 2: a principal cut on a conjunction.
--
-- The left premise ends with ⊢∧ and the right premise with ∧₁⊢, so the cut
-- formula (p ∧ q)^ε is principal on both sides: this is the case that the
-- Mix Lemma reduces to cuts on the immediate subformulae.
--
--      p^ε ⊢ p^ε   q^ε ⊢ q^ε             p^ε ⊢ p^ε
--      ---------------------- ⊢∧      --------------- ∧₁⊢
--      p^ε, q^ε ⊢ (p ∧ q)^ε           (p ∧ q)^ε ⊢ p^ε
--      ------------------------------------------------ Cut
--                    p^ε, q^ε ⊢ p^ε

q : Formula
q = Atom 1

leftPrincipal : ([ p ^ ∅ ] ,, [ q ^ ∅ ]) ⊢ [ (p ∧ q) ^ ∅ ]
leftPrincipal = ⊢∧ {Δ₁ = []} {Δ₂ = []} Ax Ax

rightPrincipal : [ (p ∧ q) ^ ∅ ] ⊢ [ p ^ ∅ ]
rightPrincipal = ∧₁⊢ {Γ = []} {B = q} Ax

principalCut : (([ p ^ ∅ ] ,, [ q ^ ∅ ]) ,, []) ⊢ ([ p ^ ∅ ] ,, [])
principalCut = Cut {A = p ∧ q} {s = ∅} leftPrincipal rightPrincipal

principal-has-cut : δ principalCut ≡ suc (degree (p ∧ q))
principal-has-cut = refl

-- MEASUREMENT (2026-08-18, Agda 2.9.0, cubical 0.9, x86_64 Linux, warm
-- interface caches, heap cap 14 GB, command
--   agda +RTS -M14G -s -RTS S4dot2/CutElimination/Examples.agda).
--
-- Asking for the rank of the eliminated proof by definitional conversion,
--
--     principal-cut-free : δ (fst (CutElimination principalCut)) ≡ 0
--     principal-cut-free = refl
--
-- did not finish within 30 minutes (killed by `timeout 1800`, no exit status
-- of its own).  The declaration below, which supplies the derivation together
-- with the cut-freeness certificate carried by the statement of the theorem,
-- elaborates from the type of CutElimination and needs no normalisation of
-- its body: it is not an observation of the elimination being executed.

principal-eliminated : Σ ((([ p ^ ∅ ] ,, [ q ^ ∅ ]) ,, []) ⊢ ([ p ^ ∅ ] ,, [])) isCutFree
principal-eliminated = CutElimination principalCut

------------------------------------------------------------------------
-- Example 3: a principal cut on a negation, the smallest principal pair.
--
--        p^ε ⊢ p^ε                 p^ε ⊢ p^ε
--      ------------- ⊢¬          ------------- ¬⊢
--      ⊢ (¬p)^ε, p^ε             p^ε, (¬p)^ε ⊢
--      ----------------------------------------- Cut
--                    p^ε ⊢ p^ε

leftNeg : [] ⊢ ([ (¬ p) ^ ∅ ] ,, [ p ^ ∅ ])
leftNeg = ⊢¬ {Γ = []} {Δ = [ p ^ ∅ ]} Ax

rightNeg : ([ p ^ ∅ ] ,, [ (¬ p) ^ ∅ ]) ⊢ []
rightNeg = ¬⊢ {Γ = [ p ^ ∅ ]} {Δ = []} Ax

negCut : ([] ,, ([ p ^ ∅ ] ,, [])) ⊢ ([ p ^ ∅ ] ,, [])
negCut = Cut {A = ¬ p} {s = ∅} leftNeg rightNeg

neg-has-cut : δ negCut ≡ suc (degree (¬ p))
neg-has-cut = refl

-- The rank of the eliminated proof is again certified by the theorem itself.
neg-eliminated : Σ (([] ,, ([ p ^ ∅ ] ,, [])) ⊢ ([ p ^ ∅ ] ,, [])) isCutFree
neg-eliminated = CutElimination negCut

-- MEASUREMENT.  Asking instead for
--
--     neg-cut-free : δ (fst (CutElimination negCut)) ≡ 0
--     neg-cut-free = refl
--
-- is rejected in 3.8 s with an [UnequalTerms] error: the left-hand side is
-- stuck on a `transp_⊢_` applied at i0, that is, on a transport introduced by
-- the reassociation of the contexts, which blocks the reduction of δ.  So on
-- this principal input the equality does not hold by definitional conversion,
-- and Agda says so quickly.  On the conjunctive principal input of Example 2
-- the same question instead did not finish within 30 minutes under a 14 GB
-- heap bound.  Both are bounded observations about definitional normalisation
-- in the present formalisation; neither is evidence of nontermination.

------------------------------------------------------------------------
-- Example 4: a non-principal cut.
--
-- The cut formula p^ε is introduced by an axiom on the right, but the left
-- proof ends with a weakening, so the cut is not principal on that side and
-- the reduction is the structural one: descend into the premise, then reapply
-- the weakening to the result.
--
--        p^ε ⊢ p^ε
--      -------------- W⊢
--      p^ε, q^ε ⊢ p^ε          p^ε ⊢ p^ε
--      ------------------------------------ Cut
--            p^ε, q^ε ⊢ p^ε

leftWeak : ([ p ^ ∅ ] ,, [ q ^ ∅ ]) ⊢ [ p ^ ∅ ]
leftWeak = W⊢ {Γ = [ p ^ ∅ ]} {Δ = [ p ^ ∅ ]} {A = q} {s = ∅} Ax

-- The implicit contexts of Cut have to be given: ,, is list append, which is
-- not invertible, so they cannot be inferred from the conclusion.
nonPrincipalCut : (([ p ^ ∅ ] ,, [ q ^ ∅ ]) ,, []) ⊢ ([] ,, [ p ^ ∅ ])
nonPrincipalCut =
  Cut {Γ₁ = [ p ^ ∅ ] ,, [ q ^ ∅ ]} {A = p} {s = ∅}
      {Δ₁ = []} {Γ₂ = []} {Δ₂ = [ p ^ ∅ ]}
      leftWeak Ax

nonprincipal-has-cut : δ nonPrincipalCut ≡ suc (degree p)
nonprincipal-has-cut = refl

nonprincipal-cut-free : δ (fst (CutElimination nonPrincipalCut)) ≡ 0
nonprincipal-cut-free = refl
